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

Let `R` be a local ring with infinite residue field, `S` an `R`-algebra with finitely many
maximal ideals containing the extension of the maximal ideal of `R`, and `M` a finite free
`S`-module. This file proves that an `R`-submodule spanning `M` over `S` contains an `S`-basis,
following [Stacks 03C1](https://stacks.math.columbia.edu/tag/03C1).
-/

open Submodule

section BasisOfSpan

variable {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M]

/-- A spanning family of cardinality `r` in a finite free module of rank `r` determines a basis. -/
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
    exact hinj (congrArg b.equivFun haa')
  exact (Pi.basisFun S (Fin r)).map (LinearEquiv.ofBijective φ ⟨hφinj, hφsurj⟩)

/-- The basis constructed by `basisOfSpanRangeEqTop` consists of the original spanning family. -/
@[simp]
theorem basisOfSpanRangeEqTop_apply [Nontrivial S] [Module.Free S M] [Module.Finite S M]
    {r : ℕ} (hr : Module.finrank S M = r) {y : Fin r → M}
    (hspan : Submodule.span S (Set.range y) = ⊤) (i : Fin r) :
    basisOfSpanRangeEqTop hr hspan i = y i := by
  classical
  set_option backward.isDefEq.respectTransparency false in
    simp only [basisOfSpanRangeEqTop, Module.Basis.map_apply, Pi.basisFun_apply,
      LinearEquiv.ofBijective_apply, Fintype.linearCombination_apply, Pi.single_apply,
      ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

end BasisOfSpan

section Nakayama

variable {S M' : Type*} [CommRing S] [AddCommGroup M'] [Module S M']

/-- A finite-family version of Nakayama's lemma for a product of ideals in the Jacobson radical. -/
theorem Submodule.eq_bot_of_forall_le_smul_of_prod_le_jacobson (Q : Submodule S M')
    (hfg : Q.FG) {s : ℕ} (n : Fin s → Ideal S) (hsmul : ∀ j, Q ≤ n j • Q)
    (hjac : (∏ j, n j) ≤ (⊥ : Ideal S).jacobson) : Q = ⊥ := by
  classical
  have hprod : ∀ t : Finset (Fin s), Q ≤ (∏ j ∈ t, n j) • Q := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty, one_smul] using (le_refl Q)
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

/-- Every element after base change to the residue field is a pure tensor with first factor one. -/
theorem exists_one_tmul_eq_residueField {N' : Type*} [AddCommGroup N'] [Module R N']
    (x : ResidueField R ⊗[R] N') : ∃ z : N', (1 : ResidueField R) ⊗ₜ[R] z = x := by
  change ∃ z : N', (1 : R ⧸ maximalIdeal R) ⊗ₜ[R] z = x
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective
    (maximalIdeal R • (⊤ : Submodule R N'))
    (quotTensorEquivQuotSMul N' (maximalIdeal R) x)
  refine ⟨z, ?_⟩
  apply (quotTensorEquivQuotSMul N' (maximalIdeal R)).injective
  simpa only [quotTensorEquivQuotSMul_mk_one_tmul] using hz

/-- A nonzero element remains nonzero as a pure tensor when the maximal ideal kills its module. -/
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

/-- A nonzero linear map into a module killed by the maximal ideal remains nonzero after base
change. -/
theorem baseChange_ne_zero_of_ne_zero_of_smul_top_eq_bot {N' T : Type*}
    [AddCommGroup N'] [Module R N'] [AddCommGroup T] [Module R T]
    (hmT : maximalIdeal R • (⊤ : Submodule R T) = ⊥) (f : N' →ₗ[R] T) {x : N'}
    (hx : f x ≠ 0) : LinearMap.baseChange (ResidueField R) f ≠ 0 := by
  intro hzero
  refine one_tmul_ne_zero_of_smul_top_eq_bot hmT hx ?_
  rw [show ((1 : ResidueField R) ⊗ₜ[R] (f x) : ResidueField R ⊗[R] T)
      = LinearMap.baseChange (ResidueField R) f (1 ⊗ₜ[R] x) from
    (LinearMap.baseChange_tmul _ _ _).symm, hzero, LinearMap.zero_apply]

/-- Over an infinite residue field, one pure tensor simultaneously avoids finitely many kernels. -/
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
    obtain ⟨z, rfl⟩ := exists_one_tmul_eq_residueField x
    obtain ⟨j, hj⟩ := hcon z
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  obtain ⟨j, hj⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hcover
  exact hne j (LinearMap.ker_eq_top.mp hj)

end Avoidance

section Semilocal

open IsLocalRing TensorProduct

variable {R : Type*} [CommRing R] [IsLocalRing R] [Infinite (ResidueField R)]
variable {S : Type*} [CommRing S] [Nontrivial S] [Algebra R S]
variable {M : Type*} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Free S M] [Module.Finite S M]

private noncomputable def fibreEval (n : Ideal S) : M →ₗ[S] (S ⧸ n) ⊗[S] M :=
  TensorProduct.mk S (S ⧸ n) M 1

omit [Nontrivial S] [Module.Free S M] [Module.Finite S M] in
private theorem fibreEval_apply (n : Ideal S) (x : M) :
    fibreEval (M := M) n x = (1 : S ⧸ n) ⊗ₜ[S] x := rfl

omit [Module.Finite S M] in
private theorem finrank_fibre (n : Ideal S) [Nontrivial (S ⧸ n)] {r : ℕ}
    (hr : Module.finrank S M = r) :
    Module.finrank (S ⧸ n) ((S ⧸ n) ⊗[S] M) = r := by
  rw [Module.finrank_baseChange, hr]

omit [IsLocalRing R] [Infinite (ResidueField R)] [Nontrivial S] [Algebra R S]
  [IsScalarTower R S M] [Module.Free S M] [Module.Finite S M] in
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
private theorem maximalIdeal_smul_quotient_fibre_eq_bot (n : Ideal S)
    (hmn : (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≤ n)
    (W : Submodule S ((S ⧸ n) ⊗[S] M)) :
    IsLocalRing.maximalIdeal R • (⊤ : Submodule R (((S ⧸ n) ⊗[S] M) ⧸ W)) = ⊥ := by
  rw [eq_bot_iff]
  refine Submodule.smul_le.mpr fun c hc x _ => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
    maximalIdeal_smul_fibre n hmn hc v, Submodule.Quotient.mk_zero]

omit [IsLocalRing R] [Infinite (ResidueField R)] [Algebra R S] [IsScalarTower R S M]
  [Module.Finite S M] in
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
private theorem linearIndependent_fibreEval_cons (n : Ideal S) (hn : n.IsMaximal)
    {t : ℕ} {y : Fin t → M} {z : M}
    (hyind : LinearIndependent (S ⧸ n) (fun i => fibreEval (M := M) n (y i)))
    (hzW : fibreEval (M := M) n z ∉
      Submodule.span (S ⧸ n) (Set.range (fun i => fibreEval (M := M) n (y i)))) :
    LinearIndependent (S ⧸ n)
      (fun i => fibreEval (M := M) n ((Fin.cons z y : Fin (t + 1) → M) i)) := by
  haveI := hn
  have hcomp : (fun i => fibreEval (M := M) n ((Fin.cons z y : Fin (t + 1) → M) i)) =
      Fin.cons (fibreEval (M := M) n z) (fun i => fibreEval (M := M) n (y i)) := by
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

omit [Module.Finite S M] in
private theorem exists_mem_forall_fibreEval_notMem_span {s : ℕ} (n : Fin s → Ideal S)
    (hnmax : ∀ j, (n j).IsMaximal)
    (hmn : ∀ j, (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≤ n j)
    (N : Submodule R M) (hN : Submodule.span S (N : Set M) = ⊤) {r t : ℕ}
    (hr : Module.finrank S M = r) (ht : t < r) {y : Fin t → M}
    (hyind : ∀ j, LinearIndependent (S ⧸ n j)
      (fun i => fibreEval (M := M) (n j) (y i))) :
    ∃ z ∈ N, ∀ j, fibreEval (M := M) (n j) z ∉
      Submodule.span (S ⧸ n j) (Set.range (fun i => fibreEval (M := M) (n j) (y i))) := by
  let W : ∀ j, Submodule (S ⧸ n j) ((S ⧸ n j) ⊗[S] M) := fun j =>
    Submodule.span (S ⧸ n j) (Set.range (fun i => fibreEval (M := M) (n j) (y i)))
  let T : Fin s → Type _ := fun j => ((S ⧸ n j) ⊗[S] M) ⧸ ((W j).restrictScalars S)
  let h : ∀ j, N →ₗ[R] T j := fun j =>
    ((((W j).restrictScalars S).mkQ.restrictScalars R).comp
      ((fibreEval (M := M) (n j)).restrictScalars R)).comp N.subtype
  have hWproper : ∀ j, ∃ z ∈ N, fibreEval (M := M) (n j) z ∉ W j := fun j =>
    exists_fibreEval_notMem_span (n j) (hnmax j) N hN hr ht (hyind j)
  have hne : ∀ j, LinearMap.baseChange (ResidueField R) (h j) ≠ 0 := by
    intro j
    obtain ⟨z, hzN, hzW⟩ := hWproper j
    refine baseChange_ne_zero_of_ne_zero_of_smul_top_eq_bot
      (maximalIdeal_smul_quotient_fibre_eq_bot (n j) (hmn j) ((W j).restrictScalars S))
      (h j) (x := ⟨z, hzN⟩) fun h0 => ?_
    exact hzW ((Submodule.Quotient.mk_eq_zero ((W j).restrictScalars S)).mp h0)
  obtain ⟨z, hz⟩ := exists_one_tmul_baseChange_ne_zero h hne
  refine ⟨z, z.2, fun j hmem => hz j ?_⟩
  rw [LinearMap.baseChange_tmul,
    show h j z = 0 from (Submodule.Quotient.mk_eq_zero _).mpr hmem,
    TensorProduct.tmul_zero]

omit [Module.Finite S M] in
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
    obtain ⟨z, hzN, hzW⟩ :=
      exists_mem_forall_fibreEval_notMem_span n hnmax hmn N hN hr ht hyind
    refine ⟨Fin.cons z y, fun i => ?_, fun j => ?_⟩
    · refine Fin.cases ?_ (fun i' => ?_) i
      · rw [Fin.cons_zero]; exact hzN
      · rw [Fin.cons_succ]; exact hyN i'
    · exact linearIndependent_fibreEval_cons (n j) (hnmax j) (hyind j) (hzW j)

omit [IsLocalRing R] [Infinite (ResidueField R)] [Nontrivial S] [Algebra R S] [Module R M]
  [IsScalarTower R S M] [Module.Free S M] [Module.Finite S M] in
private theorem fibreEval_eq_zero_iff (n : Ideal S) (x : M) :
    fibreEval (M := M) n x = 0 ↔ x ∈ n • (⊤ : Submodule S M) := by
  have hev : quotTensorEquivQuotSMul M n (fibreEval (M := M) n x)
      = Submodule.Quotient.mk x := by
    rw [fibreEval_apply, show (1 : S ⧸ n) = Ideal.Quotient.mk n 1 from (map_one _).symm,
      quotTensorEquivQuotSMul_mk_tmul, one_smul]
  rw [← Submodule.Quotient.mk_eq_zero (n • (⊤ : Submodule S M)) (x := x), ← hev,
    map_eq_zero_iff _ (quotTensorEquivQuotSMul M n).injective]

omit [IsLocalRing R] [Infinite (ResidueField R)] [Algebra R S] [Module R M]
  [IsScalarTower R S M] in
private theorem span_fibreEval_range_eq_top (n : Ideal S) (hn : n.IsMaximal) {r : ℕ}
    (hr : Module.finrank S M = r) {y : Fin r → M}
    (hyind : LinearIndependent (S ⧸ n) (fun i => fibreEval (M := M) n (y i))) :
    Submodule.span (S ⧸ n) (Set.range (fun i => fibreEval (M := M) n (y i))) = ⊤ := by
  letI : Field (S ⧸ n) := Ideal.Quotient.field n
  haveI : FiniteDimensional (S ⧸ n) ((S ⧸ n) ⊗[S] M) :=
    Module.Finite.base_change S (S ⧸ n) M
  refine hyind.span_eq_top_of_card_eq_finrank' ?_
  rw [Fintype.card_fin, finrank_fibre (M := M) n hr]

omit [IsLocalRing R] [Infinite (ResidueField R)] [Nontrivial S] [Algebra R S] [Module R M]
  [IsScalarTower R S M] [Module.Free S M] [Module.Finite S M] in
private theorem span_sup_smul_eq_top_of_span_fibreEval_eq_top (n : Ideal S) {r : ℕ}
    {y : Fin r → M}
    (hspan : Submodule.span (S ⧸ n)
      (Set.range (fun i => fibreEval (M := M) n (y i))) = ⊤) :
    Submodule.span S (Set.range y) ⊔ (n • (⊤ : Submodule S M)) = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro x -
  have hx : fibreEval (M := M) n x ∈ Submodule.span (S ⧸ n)
      (Set.range (fun i => fibreEval (M := M) n (y i))) := hspan ▸ Submodule.mem_top
  rw [Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, hc⟩ := hx
  choose cS hcS using fun i => Ideal.Quotient.mk_surjective (I := n) (c i)
  have hker : fibreEval (M := M) n (x - ∑ i, cS i • y i) = 0 := by
    rw [map_sub, map_sum]
    rw [Finset.sum_congr rfl fun i _ => by
      rw [LinearMap.map_smul,
        ← algebraMap_smul (S ⧸ n) (cS i) (fibreEval (M := M) n (y i)),
        Ideal.Quotient.algebraMap_eq, hcS i], hc, sub_self]
  rw [fibreEval_eq_zero_iff] at hker
  have hsum : (∑ i, cS i • y i) ∈ Submodule.span S (Set.range y) :=
    Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have : x = (∑ i, cS i • y i) + (x - ∑ i, cS i • y i) := by abel
  rw [this]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hsum) (Submodule.mem_sup_right hker)

omit [IsLocalRing R] [Infinite (ResidueField R)] [Nontrivial S] [Algebra R S] [Module R M]
  [IsScalarTower R S M] [Module.Free S M] in
private theorem eq_top_of_forall_sup_smul_eq_top {s : ℕ} (n : Fin s → Ideal S)
    (hnall : ∀ P : Ideal S, P.IsMaximal → ∃ j, n j = P) (P : Submodule S M)
    (hPfull : ∀ j, P ⊔ (n j • (⊤ : Submodule S M)) = ⊤) : P = ⊤ := by
  haveI : Module.Finite S (M ⧸ P) :=
    Module.Finite.of_surjective P.mkQ (Submodule.Quotient.mk_surjective P)
  have hquot : ∀ j, (⊤ : Submodule S (M ⧸ P)) ≤ n j • (⊤ : Submodule S (M ⧸ P)) := by
    intro j
    have hmap := (Submodule.map_mkQ_eq_top P (n j • (⊤ : Submodule S M))).mpr (hPfull j)
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at hmap
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

/-- A generating submodule contains a basis over a semilocal algebra satisfying the stated
hypotheses. -/
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
  have hPtop : Submodule.span S (Set.range y) = ⊤ :=
    eq_top_of_forall_sup_smul_eq_top n hnall _ fun j =>
      span_sup_smul_eq_top_of_span_fibreEval_eq_top (n j)
        (span_fibreEval_range_eq_top (n j) (hnmax j) hr (hyind j))
  exact ⟨y, hyN, basisOfSpanRangeEqTop hr hPtop,
    fun i => basisOfSpanRangeEqTop_apply hr hPtop i⟩

end Semilocal
