/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.GroupTheory.CosetCover
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite

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

set_option backward.isDefEq.respectTransparency false in
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

/-- A nonzero `R`-linear map into a module killed by the maximal ideal stays nonzero after
base change to the residue field: `1 ⊗ (f x)` witnesses non-vanishing via
`one_tmul_ne_zero_of_smul_top_eq_bot`. -/
theorem baseChange_ne_zero_of_ne_zero_of_smul_top_eq_bot {N' T : Type*}
    [AddCommGroup N'] [Module R N'] [AddCommGroup T] [Module R T]
    (hmT : maximalIdeal R • (⊤ : Submodule R T) = ⊥) (f : N' →ₗ[R] T) {x : N'}
    (hx : f x ≠ 0) : LinearMap.baseChange (ResidueField R) f ≠ 0 := by
  intro hzero
  refine one_tmul_ne_zero_of_smul_top_eq_bot hmT hx ?_
  rw [show ((1 : ResidueField R) ⊗ₜ[R] (f x) : ResidueField R ⊗[R] T)
      = LinearMap.baseChange (ResidueField R) f (1 ⊗ₜ[R] x) from
    (LinearMap.baseChange_tmul _ _ _).symm, hzero, LinearMap.zero_apply]

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

section Semilocal

open IsLocalRing TensorProduct

variable {R : Type*} [CommRing R] [IsLocalRing R] [Infinite (ResidueField R)]
variable {S : Type*} [CommRing S] [Nontrivial S] [Algebra R S]
variable {M : Type*} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Free S M] [Module.Finite S M]

/-- The evaluation of `M` in the fibre at a maximal ideal `n` of `S`, as an `S`-linear map
`M →ₗ[S] (S⧸n) ⊗[S] M`. -/
private noncomputable def fibreEval (n : Ideal S) : M →ₗ[S] (S ⧸ n) ⊗[S] M :=
  TensorProduct.mk S (S ⧸ n) M 1

omit [Nontrivial S] [Module.Free S M] [Module.Finite S M] in
private theorem fibreEval_apply (n : Ideal S) (x : M) :
    fibreEval (M := M) n x = (1 : S ⧸ n) ⊗ₜ[S] x := rfl

/-- The fibre of a free module is free of the same rank. -/
private theorem finrank_fibre (n : Ideal S) [Nontrivial (S ⧸ n)] {r : ℕ}
    (hr : Module.finrank S M = r) :
    Module.finrank (S ⧸ n) ((S ⧸ n) ⊗[S] M) = r := by
  classical
  have b := (Module.finBasis S M).reindex (finCongr hr)
  rw [Module.finrank_eq_card_basis (b.baseChange (S ⧸ n)), Fintype.card_fin]

omit [IsLocalRing R] [Infinite (ResidueField R)] [Nontrivial S] [Algebra R S]
  [IsScalarTower R S M] [Module.Free S M] [Module.Finite S M] in
/-- If `N` generates `M` over `S`, its fibre image spans the fibre. -/
private theorem span_fibreEval_eq_top (n : Ideal S) (N : Submodule R M)
    (hN : Submodule.span S (N : Set M) = ⊤) :
    Submodule.span (S ⧸ n) (fibreEval (M := M) n '' (N : Set M)) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x with
  | zero => exact Submodule.zero_mem _
  | tmul c z =>
    have hz : z ∈ Submodule.span S (N : Set M) := hN ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem w hw =>
      have : (c ⊗ₜ[S] w : (S ⧸ n) ⊗[S] M) = c • fibreEval (M := M) n w := by
        rw [fibreEval_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ c (Submodule.subset_span ⟨w, hw, rfl⟩)
    | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | add u v _ _ ihu ihv =>
      rw [TensorProduct.tmul_add]
      exact Submodule.add_mem _ ihu ihv
    | smul s u _ ihu =>
      rw [TensorProduct.tmul_smul]
      exact Submodule.smul_of_tower_mem _ s ihu
  | add x y ihx ihy => exact Submodule.add_mem _ ihx ihy

omit [Infinite (ResidueField R)] [Nontrivial S] [Module R M] [IsScalarTower R S M]
  [Module.Free S M] [Module.Finite S M] in
/-- The maximal ideal of `R` acts as zero on the fibre at `n` when `m·S ≤ n`: the scalar
travels through `S → S⧸n`, where it dies. -/
private theorem maximalIdeal_smul_fibre (n : Ideal S)
    (hmn : (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≤ n)
    {c : R} (hc : c ∈ IsLocalRing.maximalIdeal R) (v : (S ⧸ n) ⊗[S] M) : c • v = 0 := by
  induction v with
  | zero => rw [smul_zero]
  | tmul a m =>
    rw [TensorProduct.smul_tmul', Algebra.smul_def,
      IsScalarTower.algebraMap_apply R S (S ⧸ n),
      show (algebraMap S (S ⧸ n)) (algebraMap R S c) = 0 from
        Ideal.Quotient.eq_zero_iff_mem.mpr (hmn (Ideal.mem_map_of_mem _ hc)),
      zero_mul, TensorProduct.zero_tmul]
  | add x y ihx ihy => rw [smul_add, ihx, ihy, add_zero]

omit [Infinite (ResidueField R)] [Nontrivial S] [Module.Free S M] [Module.Finite S M] in
/-- The maximal ideal of `R` kills any `R`-quotient of the fibre `(S⧸n) ⊗ M` when `m·S ≤ n`,
since it already kills the fibre itself (`maximalIdeal_smul_fibre`). -/
private theorem maximalIdeal_smul_quotient_fibre_eq_bot (n : Ideal S)
    (hmn : (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≤ n)
    (W : Submodule S ((S ⧸ n) ⊗[S] M)) :
    IsLocalRing.maximalIdeal R • (⊤ : Submodule R (((S ⧸ n) ⊗[S] M) ⧸ W)) = ⊥ := by
  rw [eq_bot_iff]
  refine Submodule.smul_le.mpr fun c hc x _ => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
    maximalIdeal_smul_fibre n hmn hc v, Submodule.Quotient.mk_zero]

omit [IsLocalRing R] [Infinite (ResidueField R)] [Algebra R S] [IsScalarTower R S M] in
/-- **The properness of the current fibre span** (the counting step of Stacks 03C1's
general-position induction): if the images `fibreEval n (y i)` are linearly independent in the
fibre at a maximal ideal `n` and there are strictly fewer of them than `r = finrank S M`, then
their span is proper, so some `z ∈ N` has `fibreEval n z` outside it — otherwise those `t`
vectors would be a basis of the `r`-dimensional fibre. -/
private theorem exists_fibreEval_notMem_span (n : Ideal S) (hn : n.IsMaximal)
    (N : Submodule R M) (hN : Submodule.span S (N : Set M) = ⊤)
    {r : ℕ} (hr : Module.finrank S M = r) {t : ℕ} (ht : t < r) {y : Fin t → M}
    (hyind : LinearIndependent (S ⧸ n) (fun i => fibreEval (M := M) n (y i))) :
    ∃ z ∈ N, fibreEval (M := M) n z ∉
      Submodule.span (S ⧸ n) (Set.range (fun i => fibreEval (M := M) n (y i))) := by
  by_contra hcon
  push Not at hcon
  haveI : Nontrivial (S ⧸ n) := Ideal.Quotient.nontrivial_iff.mpr hn.ne_top
  have hle : (⊤ : Submodule (S ⧸ n) ((S ⧸ n) ⊗[S] M)) ≤
      Submodule.span (S ⧸ n) (Set.range (fun i => fibreEval (M := M) n (y i))) := by
    rw [← span_fibreEval_eq_top n N hN, Submodule.span_le]
    rintro - ⟨z, hz, rfl⟩
    exact hcon z hz
  have hbasis := Module.Basis.mk hyind hle
  have hcard := Module.finrank_eq_card_basis hbasis
  rw [finrank_fibre (M := M) n hr, Fintype.card_fin] at hcard
  omega

omit [Nontrivial S] [Module.Free S M] [Module.Finite S M] in
/-- **Extending a fibre-independent family**: if `fibreEval n ∘ y` is linearly independent in
the fibre at a maximal ideal `n` and `fibreEval n z` escapes its span, then prepending `z`
keeps the family fibre-independent — the escaping element cannot be a linear combination of the
others, using that `S⧸n` is a field. -/
private theorem linearIndependent_fibreEval_cons (n : Ideal S) (hn : n.IsMaximal)
    {t : ℕ} {y : Fin t → M} {z : M}
    (hyind : LinearIndependent (S ⧸ n) (fun i => fibreEval (M := M) n (y i)))
    (hzW : fibreEval (M := M) n z ∉
      Submodule.span (S ⧸ n) (Set.range (fun i => fibreEval (M := M) n (y i)))) :
    LinearIndependent (S ⧸ n)
      (fun i => fibreEval (M := M) n ((Fin.cons z y : Fin (t + 1) → M) i)) := by
  haveI := hn
  have hcomp : (fun i => fibreEval (M := M) n ((Fin.cons z y : Fin (t + 1) → M) i))
      = Fin.cons (fibreEval (M := M) n z) (fun i => fibreEval (M := M) n (y i)) := by
    funext i
    refine Fin.cases ?_ (fun i' => ?_) i
    · rw [Fin.cons_zero, Fin.cons_zero]
    · rw [Fin.cons_succ, Fin.cons_succ]
  rw [hcomp]
  refine LinearIndependent.finCons' _ _ hyind ?_
  intro c w hw hsum
  by_contra hc0
  obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv hc0
  refine hzW ?_
  have hx : c • fibreEval (M := M) n z = -w := eq_neg_of_add_eq_zero_left hsum
  have hbc : fibreEval (M := M) n z = b • (c • fibreEval (M := M) n z) := by
    rw [smul_smul, show b * c = 1 from (mul_comm c b) ▸ hb, one_smul]
  rw [hbc, hx]
  exact Submodule.smul_mem _ b (Submodule.neg_mem _ hw)

/-- **The general-position induction of Stacks 03C1**: for each `t ≤ r` there is a family
of `t` elements of `N` whose images in every fibre `(S⧸nⱼ) ⊗ M` are linearly independent.
The step escapes the `t`-dimensional spans in all fibres simultaneously via
`exists_one_tmul_baseChange_ne_zero`. -/
private theorem exists_fibre_independent {s : ℕ} (n : Fin s → Ideal S)
    (hnmax : ∀ j, (n j).IsMaximal)
    (hmn : ∀ j, (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≤ n j)
    (N : Submodule R M) (hN : Submodule.span S (N : Set M) = ⊤) {r : ℕ}
    (hr : Module.finrank S M = r) :
    ∀ t : ℕ, t ≤ r → ∃ y : Fin t → M, (∀ i, y i ∈ N) ∧
      ∀ j, LinearIndependent (S ⧸ n j) (fun i => fibreEval (M := M) (n j) (y i)) := by
  intro t
  induction t with
  | zero =>
    exact fun _ => ⟨Fin.elim0, fun i => i.elim0, fun j => linearIndependent_empty_type⟩
  | succ t ih =>
    intro ht
    obtain ⟨y, hyN, hyind⟩ := ih (Nat.le_of_succ_le ht)
    -- the current spans in each fibre, and the quotient targets
    let W : ∀ j, Submodule (S ⧸ n j) ((S ⧸ n j) ⊗[S] M) := fun j =>
      Submodule.span (S ⧸ n j) (Set.range (fun i => fibreEval (M := M) (n j) (y i)))
    let T : Fin s → Type _ := fun j =>
      ((S ⧸ n j) ⊗[S] M) ⧸ ((W j).restrictScalars S)
    let h : ∀ j, N →ₗ[R] T j := fun j =>
      ((((W j).restrictScalars S).mkQ.restrictScalars R).comp
        ((fibreEval (M := M) (n j)).restrictScalars R)).comp N.subtype
    -- each fibre span is proper (else t independent vectors would be a basis, so r = t),
    -- giving an element of N escaping it
    have hWproper : ∀ j, ∃ z ∈ N, fibreEval (M := M) (n j) z ∉ W j := fun j =>
      exists_fibreEval_notMem_span (n j) (hnmax j) N hN hr ht (hyind j)
    -- the maps into the quotients by the spans are nonzero after residue base change
    have hne : ∀ j, LinearMap.baseChange (ResidueField R) (h j) ≠ 0 := by
      intro j
      obtain ⟨z, hzN, hzW⟩ := hWproper j
      refine baseChange_ne_zero_of_ne_zero_of_smul_top_eq_bot
        (maximalIdeal_smul_quotient_fibre_eq_bot (n j) (hmn j) ((W j).restrictScalars S))
        (h j) (x := ⟨z, hzN⟩) ?_
      intro h0
      exact hzW (by
        have := (Submodule.Quotient.mk_eq_zero ((W j).restrictScalars S)).mp h0
        exact this)
    -- escape all fibres at once
    obtain ⟨z, hz⟩ := exists_one_tmul_baseChange_ne_zero h hne
    have hzW : ∀ j, fibreEval (M := M) (n j) (z : M) ∉ W j := by
      intro j hmem
      refine hz j ?_
      rw [LinearMap.baseChange_tmul,
        show h j z = 0 from (Submodule.Quotient.mk_eq_zero _).mpr hmem,
        TensorProduct.tmul_zero]
    -- extend the family
    refine ⟨Fin.cons (z : M) y, fun i => ?_, fun j => ?_⟩
    · refine Fin.cases ?_ (fun i' => ?_) i
      · rw [Fin.cons_zero]; exact z.2
      · rw [Fin.cons_succ]; exact hyN i'
    · exact linearIndependent_fibreEval_cons (n j) (hnmax j) (hyind j) (hzW j)

omit [IsLocalRing R] [Infinite (ResidueField R)] [Nontrivial S] [Algebra R S] [Module R M]
  [IsScalarTower R S M] [Module.Free S M] [Module.Finite S M] in
/-- An element evaluates to zero in the fibre at `n` iff it lies in `n•M`: transport the
kernel of `M → M ⧸ n•M` along `quotTensorEquivQuotSMul`. -/
private theorem fibreEval_eq_zero_iff (n : Ideal S) (x : M) :
    fibreEval (M := M) n x = 0 ↔ x ∈ n • (⊤ : Submodule S M) := by
  have hev : quotTensorEquivQuotSMul M n (fibreEval (M := M) n x)
      = Submodule.Quotient.mk x := by
    rw [fibreEval_apply, show (1 : S ⧸ n) = Ideal.Quotient.mk n 1 from (map_one _).symm,
      quotTensorEquivQuotSMul_mk_tmul, one_smul]
  rw [← Submodule.Quotient.mk_eq_zero (n • (⊤ : Submodule S M)) (x := x), ← hev,
    map_eq_zero_iff _ (quotTensorEquivQuotSMul M n).injective]

/-- **Selecting a basis from a generating submodule over a semi-local ring**
(Stacks 03C1, tag `algebra-lemma-semi-local-module-basis-in-submodule`): `R` local with
infinite residue field, `S` an `R`-algebra whose maximal ideals are exactly the finitely
many `n j`, each containing `m·S`, and `M` finite free over `S` of rank `r`. If the
`R`-submodule `N` generates `M` over `S`, then `N` contains an `S`-basis of `M`. -/
theorem Submodule.exists_basis_mem_of_span_eq_top {s : ℕ} (n : Fin s → Ideal S)
    (hnmax : ∀ j, (n j).IsMaximal)
    (hnall : ∀ P : Ideal S, P.IsMaximal → ∃ j, n j = P)
    (hmn : ∀ j, (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≤ n j)
    {r : ℕ} (hr : Module.finrank S M = r)
    (N : Submodule R M) (hN : Submodule.span S (N : Set M) = ⊤) :
    ∃ y : Fin r → M, (∀ i, y i ∈ N) ∧
      ∃ b : Module.Basis (Fin r) S M, ∀ i, b i = y i := by
  classical
  obtain ⟨y, hyN, hyind⟩ :=
    exists_fibre_independent n hnmax hmn N hN hr r le_rfl
  -- the selected family spans each fibre
  have hfibrespan : ∀ j, Submodule.span (S ⧸ n j)
      (Set.range (fun i => fibreEval (M := M) (n j) (y i))) = ⊤ := by
    intro j
    haveI : Nontrivial (S ⧸ n j) := Ideal.Quotient.nontrivial_iff.mpr (hnmax j).ne_top
    letI : Field (S ⧸ n j) := Ideal.Quotient.field (n j)
    haveI : FiniteDimensional (S ⧸ n j) ((S ⧸ n j) ⊗[S] M) :=
      Module.Finite.base_change S (S ⧸ n j) M
    refine (hyind j).span_eq_top_of_card_eq_finrank' ?_
    rw [Fintype.card_fin, finrank_fibre (M := M) (n j) hr]
  -- hence P := span y is full modulo each nⱼ•M
  set P : Submodule S M := Submodule.span S (Set.range y) with hP
  have hPfull : ∀ j, P ⊔ (n j • (⊤ : Submodule S M)) = ⊤ := by
    intro j
    rw [eq_top_iff]
    rintro x -
    have hx : fibreEval (M := M) (n j) x ∈ Submodule.span (S ⧸ n j)
        (Set.range (fun i => fibreEval (M := M) (n j) (y i))) := by
      rw [hfibrespan j]; exact Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨c, hc⟩ := hx
    choose cS hcS using fun i => Ideal.Quotient.mk_surjective (I := n j) (c i)
    have hker : fibreEval (M := M) (n j) (x - ∑ i, cS i • y i) = 0 := by
      rw [map_sub, map_sum]
      have hterm : ∀ i, fibreEval (M := M) (n j) (cS i • y i)
          = c i • fibreEval (M := M) (n j) (y i) := by
        intro i
        rw [LinearMap.map_smul,
          ← algebraMap_smul (S ⧸ n j) (cS i) (fibreEval (M := M) (n j) (y i)),
          Ideal.Quotient.algebraMap_eq, hcS i]
      rw [Finset.sum_congr rfl fun i _ => hterm i, hc, sub_self]
    rw [fibreEval_eq_zero_iff] at hker
    have hsum : (∑ i, cS i • y i) ∈ P :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨i, rfl⟩)
    have : x = (∑ i, cS i • y i) + (x - ∑ i, cS i • y i) := by abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hsum) (Submodule.mem_sup_right hker)
  -- family Nakayama on M ⧸ P forces P = ⊤
  have hPtop : P = ⊤ := by
    haveI : Module.Finite S (M ⧸ P) :=
      Module.Finite.of_surjective P.mkQ (Submodule.Quotient.mk_surjective P)
    have hquot : ∀ j,
        (⊤ : Submodule S (M ⧸ P)) ≤ n j • (⊤ : Submodule S (M ⧸ P)) := by
      intro j
      have hmap := congrArg (Submodule.map P.mkQ) (hPfull j)
      rw [Submodule.map_sup, Submodule.map_smul'', Submodule.map_top,
        Submodule.range_mkQ, show Submodule.map P.mkQ P = ⊥ by
          rw [eq_bot_iff]
          rintro - ⟨p, hp, rfl⟩
          rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact hp] at hmap
      rw [bot_sup_eq] at hmap
      exact le_of_eq hmap.symm
    have hbot := Submodule.eq_bot_of_forall_le_smul_of_prod_le_jacobson
      (⊤ : Submodule S (M ⧸ P)) Module.Finite.fg_top n hquot
      (by
        rw [Ideal.jacobson]
        refine le_sInf fun J hJ => ?_
        obtain ⟨j, rfl⟩ := hnall J hJ.2
        exact le_trans Ideal.prod_le_inf (Finset.inf_le (Finset.mem_univ j)))
    rw [eq_top_iff]
    intro x _
    have : P.mkQ x ∈ (⊥ : Submodule S (M ⧸ P)) := hbot ▸ Submodule.mem_top
    rwa [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  exact ⟨y, hyN, basisOfSpanRangeEqTop hr (hP ▸ hPtop),
    fun i => basisOfSpanRangeEqTop_apply hr (hP ▸ hPtop) i⟩

end Semilocal
