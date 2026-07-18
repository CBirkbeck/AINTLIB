/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.CoactionCharpoly
import ModularCurves.ForMathlib.CoinvariantsBaseChange
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.LinearAlgebra.Determinant

/-!
# Points of the co-invariants: surjectivity

Construction support for `[CHARTER-HOPF]` / `T-G3d-infra` Piece 3
(`.mathlib-quality/decomposition-hopf-crux.md`, leaf `[HG-B4]`; Stacks
`groupoids-lemma-points`, tag 03BL): the easy half — `Spec B → Spec (coinvariants ρ)` is
surjective, because `B` is integral over the co-invariants (`isIntegral_coinvariants`,
03BJ) and the inclusion is injective, so lying-over applies.

The hard half of 03BL — the `k̄`-points orbit theorem and the finitely-many-maximals
corollary — is the next increment of this file.
-/

open scoped TensorProduct

namespace ModularCurves

variable (R A : Type*) [CommRing R] [CommRing A] [HopfAlgebra R A]
  [Module.Free R A] [Module.Finite R A]
variable {B : Type*} [CommRing B] [Algebra R B]

/-- The co-invariants inclusion is an integral algebra (03BJ, instance-shaped). -/
theorem isIntegral_algebra_coinvariants (ρ : B →ₐ[R] B ⊗[R] A) (hρ : IsCoaction ρ) :
    Algebra.IsIntegral (coinvariants ρ) B :=
  ⟨fun f => isIntegral_coinvariants R A ρ hρ f⟩

/-- **03BL, surjectivity half**: every prime of the co-invariants is the restriction of a
prime of `B` — lying-over along the integral, injective inclusion. -/
theorem exists_prime_over_coinvariants (ρ : B →ₐ[R] B ⊗[R] A) (hρ : IsCoaction ρ)
    (p : Ideal (coinvariants ρ)) [p.IsPrime] :
    ∃ q : Ideal B, q.IsPrime ∧ Ideal.comap (algebraMap (coinvariants ρ) B) q = p := by
  haveI := isIntegral_algebra_coinvariants R A ρ hρ
  obtain ⟨q, -, hq, hcomap⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p ⊥ (by
    rw [Ideal.comap_bot_of_injective (algebraMap (coinvariants ρ) B)
      (Subtype.val_injective)]
    exact bot_le)
  exact ⟨q, hq, hcomap⟩

section PowerWitness

variable (ρ : B →ₐ[R] B ⊗[R] A)
variable (C'' : Type*) [CommRing C''] [Algebra R C'']
variable [Algebra (coinvariants ρ) C''] [IsScalarTower R (coinvariants ρ) C'']

/-- The invariant charpoly is the `r`-th power of `X − f`: if `f` is a co-invariant of the
base-changed co-action, its multiplication matrix is the scalar `f`, so the charpoly is
`(X − f)^r`. -/
theorem coactionCharpoly_of_mem_coinvariants (f : C'' ⊗[coinvariants ρ] B)
    (hf : f ∈ coinvariants (coactionBaseChange R A ρ C'')) :
    coactionCharpoly R A (coactionBaseChange R A ρ C'') f
      = (Polynomial.X - Polynomial.C f) ^ Fintype.card (hopfBasisIndex R A) := by
  classical
  rw [mem_coinvariants] at hf
  rw [coactionCharpoly, hf, show ((f ⊗ₜ[R] (1 : A)) :
      (C'' ⊗[coinvariants ρ] B) ⊗[R] A) = f ⊗ₜ[R] (1 : A) from rfl,
    mulMatrix_includeLeft, Matrix.charpoly_diagonal]
  rw [Finset.prod_const, Finset.card_univ]

variable {D : Type*} [CommRing D] [Algebra R D]
variable [Algebra (coinvariants ρ) D] [IsScalarTower R (coinvariants ρ) D]

omit [Module.Free R A] [Module.Finite R A] in
/-- Naturality of the base-changed co-action in the base: for a `C`-algebra map
`π : D → C''`, the co-actions intertwine through `π ⊗ id`. -/
theorem coactionBaseChange_naturality (π : D →ₐ[coinvariants ρ] C'')
    (x : D ⊗[coinvariants ρ] B) :
    coactionBaseChange R A ρ C''
        ((Algebra.TensorProduct.map π (AlgHom.id (coinvariants ρ) B)) x)
      = (Algebra.TensorProduct.map
          ((Algebra.TensorProduct.map π (AlgHom.id (coinvariants ρ) B)).restrictScalars R)
          (AlgHom.id R A))
          (coactionBaseChange R A ρ D x) := by
  induction x with
  | zero => simp
  | tmul d b =>
    rw [Algebra.TensorProduct.map_tmul]
    rw [show (AlgHom.id (coinvariants ρ) B) b = b from rfl,
      coactionBaseChange_tmul, coactionBaseChange_tmul]
    induction ρ b with
    | zero => simp [TensorProduct.tmul_zero]
    | tmul b₀ a =>
      rw [show (baseChangeAssoc R A ρ C'').symm
          (π d ⊗ₜ[coinvariants ρ] (b₀ ⊗ₜ[R] a))
          = (π d ⊗ₜ[coinvariants ρ] b₀) ⊗ₜ[R] a from
        Algebra.TensorProduct.assoc_symm_tmul _ _ _ _ _ _,
        show (baseChangeAssoc R A ρ D).symm (d ⊗ₜ[coinvariants ρ] (b₀ ⊗ₜ[R] a))
          = (d ⊗ₜ[coinvariants ρ] b₀) ⊗ₜ[R] a from
        Algebra.TensorProduct.assoc_symm_tmul _ _ _ _ _ _,
        Algebra.TensorProduct.map_tmul]
      rfl
    | add z w ihz ihw =>
      conv_rhs => rw [TensorProduct.tmul_add, map_add, map_add]
      rw [TensorProduct.tmul_add, map_add, ihz, ihw]
  | add x y ihx ihy =>
    conv_rhs => rw [map_add, map_add]
    rw [map_add, map_add, ihx, ihy]

/-- **The power witness (Stacks 03BK(2)(a), constant-coefficient form)**: for any
base change `C''` of the co-invariants and any co-invariant `f` upstairs,
`f^r` lies in the image of `C''` — lift along a flat polynomial cover, where the charpoly
coefficients are honest scalars, and map down to the expansion of `(X − f)^r`. -/
theorem pow_card_mem_range_algebraMap_of_mem_coinvariants (hρ : IsCoaction ρ)
    (f : C'' ⊗[coinvariants ρ] B)
    (hf : f ∈ coinvariants (coactionBaseChange R A ρ C'')) :
    ∃ c'' : C'', algebraMap C'' (C'' ⊗[coinvariants ρ] B) c''
      = f ^ Fintype.card (hopfBasisIndex R A) := by
  classical
  let π : MvPolynomial C'' (coinvariants ρ) →ₐ[coinvariants ρ] C'' :=
    MvPolynomial.aeval id
  have hπsurj : Function.Surjective π := fun c'' =>
    ⟨MvPolynomial.X c'', by simp [π]⟩
  let πB := Algebra.TensorProduct.map π (AlgHom.id (coinvariants ρ) B)
  have hπBsurj : Function.Surjective πB :=
    Algebra.TensorProduct.map_surjective π (AlgHom.id (coinvariants ρ) B) hπsurj
      Function.surjective_id
  obtain ⟨g, hg⟩ := hπBsurj f
  -- the charpoly upstairs has scalar coefficients (flat cover: 03BK(3))
  have hcoeffD : ∀ k, ∃ d : MvPolynomial C'' (coinvariants ρ),
      algebraMap (MvPolynomial C'' (coinvariants ρ))
        (MvPolynomial C'' (coinvariants ρ) ⊗[coinvariants ρ] B) d
      = (coactionCharpoly R A
          (coactionBaseChange R A ρ (MvPolynomial C'' (coinvariants ρ))) g).coeff k := by
    intro k
    have hmem := coactionCharpoly_coeff_mem R A
      (coactionBaseChange R A ρ (MvPolynomial C'' (coinvariants ρ)))
      (isCoaction_coactionBaseChange R A ρ (MvPolynomial C'' (coinvariants ρ)) hρ) g k
    obtain ⟨d, hd⟩ := (mem_coinvariants_coactionBaseChange_iff R A ρ
      (MvPolynomial C'' (coinvariants ρ)) _).mp hmem
    exact ⟨d, by rw [← hd]; rfl⟩
  -- transport the charpoly down along πB
  have htransport : coactionCharpoly R A (coactionBaseChange R A ρ C'') f
      = (coactionCharpoly R A
          (coactionBaseChange R A ρ (MvPolynomial C'' (coinvariants ρ))) g).map
          (πB.restrictScalars R).toRingHom := by
    rw [coactionCharpoly, coactionCharpoly, ← Matrix.charpoly_map]
    congr 1
    rw [← hg, coactionBaseChange_naturality R A ρ C'' π g]
    exact mulMatrix_map R A ((πB.restrictScalars R)) _
  -- conclude: the constant coefficient of (X − f)^r is in the image
  have hpow := coactionCharpoly_of_mem_coinvariants R A ρ C'' f hf
  obtain ⟨d₀, hd₀⟩ := hcoeffD 0
  refine ⟨(-1) ^ Fintype.card (hopfBasisIndex R A) * π d₀, ?_⟩
  have hcoeff0 : (coactionCharpoly R A (coactionBaseChange R A ρ C'') f).coeff 0
      = algebraMap C'' (C'' ⊗[coinvariants ρ] B) (π d₀) := by
    rw [htransport, Polynomial.coeff_map, ← hd₀]
    show πB (algebraMap (MvPolynomial C'' (coinvariants ρ))
      (MvPolynomial C'' (coinvariants ρ) ⊗[coinvariants ρ] B) d₀) = _
    rw [show algebraMap (MvPolynomial C'' (coinvariants ρ))
        (MvPolynomial C'' (coinvariants ρ) ⊗[coinvariants ρ] B) d₀
        = d₀ ⊗ₜ[coinvariants ρ] (1 : B) from rfl,
      show πB (d₀ ⊗ₜ[coinvariants ρ] (1 : B))
        = π d₀ ⊗ₜ[coinvariants ρ] ((AlgHom.id (coinvariants ρ) B) (1 : B)) from
      Algebra.TensorProduct.map_tmul _ _ _ _, map_one]
    rfl
  have hval : (coactionCharpoly R A (coactionBaseChange R A ρ C'') f).coeff 0
      = (-1) ^ Fintype.card (hopfBasisIndex R A)
        * f ^ Fintype.card (hopfBasisIndex R A) := by
    rw [hpow, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub, neg_pow]
  rw [map_mul, map_pow, map_neg, map_one, ← hcoeff0, hval, ← mul_assoc, ← mul_pow,
    neg_mul_neg, one_mul, one_pow, one_mul]

end PowerWitness

section Orbit

variable {k : Type*} [Field k] [Algebra R k]

omit [Module.Free R A] in
/-- The `k`-points of `B ⊗ A` lying over a fixed point `a₁` of `B` (through the left
inclusion) are finite: they biject into the `k`-points of the finite `k`-algebra
`k ⊗[B, a₁] (B ⊗ A)`. -/
theorem finite_setOf_comp_includeLeft_eq (a₁ : B →ₐ[R] k) :
    {χ : (B ⊗[R] A) →ₐ[R] k |
      χ.comp (Algebra.TensorProduct.includeLeft (S := R)) = a₁}.Finite := by
  classical
  letI : Algebra B k := a₁.toRingHom.toAlgebra
  haveI : Module.Finite B (B ⊗[R] A) := Module.Finite.base_change R B A
  haveI : FiniteDimensional k (k ⊗[B] (B ⊗[R] A)) := Module.Finite.base_change B k _
  haveI : Fintype ((k ⊗[B] (B ⊗[R] A)) →ₐ[k] k) := minpoly.AlgHom.fintype _ _ _
  set Φ : {χ : (B ⊗[R] A) →ₐ[R] k |
      χ.comp (Algebra.TensorProduct.includeLeft (S := R)) = a₁} →
      ((k ⊗[B] (B ⊗[R] A)) →ₐ[k] k) := fun χ =>
    Algebra.TensorProduct.lift (AlgHom.id k k)
      { toRingHom := (χ : (B ⊗[R] A) →ₐ[R] k).toRingHom
        commutes' := fun b => by
          have := AlgHom.congr_fun χ.2 b
          exact this }
      (fun _ _ => Commute.all _ _) with hΦ
  have hΦinj : Function.Injective Φ := by
    intro χ₁ χ₂ h
    refine Subtype.ext (AlgHom.ext fun x => ?_)
    have h1 := AlgHom.congr_fun h ((1 : k) ⊗ₜ[B] x)
    simpa [hΦ, Algebra.TensorProduct.lift_tmul] using h1
  exact Set.finite_coe_iff.mp (Finite.of_injective Φ hΦinj)

omit [Module.Free R A] [Module.Finite R A] in
/-- The co-action reflects units: the counit retraction is a left inverse. -/
theorem isUnit_of_isUnit_coaction {ρ : B →ₐ[R] B ⊗[R] A} (hρ : IsCoaction ρ) {f : B}
    (h : IsUnit (ρ f)) : IsUnit f := by
  have := h.map (counitRetraction R A)
  rwa [show (counitRetraction R A) (ρ f) = f from
    AlgHom.congr_fun (counitRetraction_comp_coaction R A ρ hρ) f] at this

/-- The multiplication matrix is the matrix of left multiplication in the base-changed
basis. -/
theorem toMatrix_lmul_eq_mulMatrix (u : B ⊗[R] A) :
    LinearMap.toMatrix ((hopfBasis R A).baseChange B) ((hopfBasis R A).baseChange B)
        (LinearMap.mulLeft B u)
      = mulMatrix R A u := by
  classical
  ext i j
  rw [LinearMap.toMatrix_apply, Module.Basis.baseChange_apply, LinearMap.mulLeft_apply,
    mul_one_tmul_hopfBasis R A u j, map_sum]
  simp [Module.Basis.baseChange_repr_tmul, Module.Basis.repr_self, Finsupp.single_apply]

/-- An invertible multiplication matrix makes the element a unit: the represented left
multiplication is then invertible, so `1` has a preimage. -/
theorem isUnit_of_isUnit_mulMatrix {u : B ⊗[R] A}
    (h : IsUnit (mulMatrix R A u)) : IsUnit u := by
  classical
  haveI : Module.Free B (B ⊗[R] A) :=
    Module.Free.of_basis ((hopfBasis R A).baseChange B)
  haveI : Module.Finite B (B ⊗[R] A) :=
    Module.Finite.of_basis ((hopfBasis R A).baseChange B)
  have hdet : IsUnit (LinearMap.det (LinearMap.mulLeft B u)) := by
    rw [← LinearMap.det_toMatrix ((hopfBasis R A).baseChange B),
      toMatrix_lmul_eq_mulMatrix]
    exact (Matrix.isUnit_iff_isUnit_det _).mp h
  obtain ⟨φ, hφ⟩ := (LinearMap.isUnit_iff_isUnit_det _).mpr hdet
  refine IsUnit.of_mul_eq_one
    ((↑φ⁻¹ : B ⊗[R] A →ₗ[B] B ⊗[R] A) (1 : B ⊗[R] A)) ?_
  have hcomp := congrFun (congrArg
    (fun (ψ : B ⊗[R] A →ₗ[B] B ⊗[R] A) => (ψ : _ → _)) φ.mul_inv) (1 : B ⊗[R] A)
  have h1 : ((↑φ * ↑φ⁻¹ : B ⊗[R] A →ₗ[B] B ⊗[R] A)) (1 : B ⊗[R] A)
      = (↑φ : B ⊗[R] A →ₗ[B] B ⊗[R] A)
          ((↑φ⁻¹ : B ⊗[R] A →ₗ[B] B ⊗[R] A) (1 : B ⊗[R] A)) := rfl
  rw [h1, hφ, LinearMap.mulLeft_apply] at hcomp
  simpa using hcomp

/-- A `k`-algebra map to `k` is determined by its kernel: `x − χ(x)` always lies in it. -/
theorem algHom_ext_of_ker_eq {X : Type*} [CommRing X] [Algebra k X]
    {χ₁ χ₂ : X →ₐ[k] k} (h : RingHom.ker χ₁.toRingHom = RingHom.ker χ₂.toRingHom) :
    χ₁ = χ₂ := by
  refine AlgHom.ext fun x => ?_
  have hmem : x - algebraMap k X (χ₁ x) ∈ RingHom.ker χ₁.toRingHom := by
    simp [RingHom.mem_ker]
  rw [h, RingHom.mem_ker] at hmem
  have h2 : χ₂ x = χ₁ x := by simpa [sub_eq_zero] using hmem
  exact h2.symm

/-- **The avoidance step** of the orbit theorem: a `k`-point not among a finite set of
`k`-points has a kernel element avoiding all their kernels (prime avoidance + kernels of
`k`-points are maximal and determine the point). -/
theorem exists_mem_ker_notMem_ker {X : Type*} [CommRing X] [Algebra k X]
    (χ₀ : X →ₐ[k] k) (S : Finset (X →ₐ[k] k)) (hS : χ₀ ∉ S) :
    ∃ f ∈ RingHom.ker χ₀.toRingHom, ∀ χ ∈ S, f ∉ RingHom.ker χ.toRingHom := by
  classical
  by_contra hcon
  push Not at hcon
  have hcover : (RingHom.ker χ₀.toRingHom : Set X)
      ⊆ ⋃ χ ∈ (S : Set (X →ₐ[k] k)), (RingHom.ker χ.toRingHom : Set X) := by
    intro f hf
    obtain ⟨χ, hχS, hχ⟩ := hcon f hf
    exact Set.mem_biUnion hχS hχ
  obtain ⟨χ, hχS, hle⟩ := (Ideal.subset_union_prime χ₀ χ₀
    (fun χ _ _ _ => RingHom.ker_isPrime _)).mp hcover
  have hsurj₀ : Function.Surjective χ₀.toRingHom := fun c =>
    ⟨algebraMap k X c, by simp⟩
  have hmax₀ : (RingHom.ker χ₀.toRingHom).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ hsurj₀
  have heq : RingHom.ker χ₀.toRingHom = RingHom.ker χ.toRingHom :=
    hmax₀.eq_of_le (RingHom.ker_isPrime _).ne_top hle
  exact hS (by rwa [algHom_ext_of_ker_eq heq])

/-- Over an algebraically closed field, an element of a finite algebra that no `k`-point
kills is a unit: otherwise it lies in a maximal ideal, whose residue field is `k` itself by
integrality and algebraic closedness. -/
theorem isUnit_of_forall_algHom_ne_zero [IsAlgClosed k] {X : Type*} [CommRing X]
    [Algebra k X] [Module.Finite k X] (u : X)
    (h : ∀ χ : X →ₐ[k] k, χ u ≠ 0) : IsUnit u := by
  classical
  by_contra hu
  obtain ⟨m, hm, hum⟩ := exists_max_ideal_of_mem_nonunits hu
  haveI : m.IsMaximal := hm
  haveI : Field (X ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.IsIntegral k (X ⧸ m) := by
    haveI : Module.Finite k (X ⧸ m) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ k m).toLinearMap
        Ideal.Quotient.mk_surjective
    exact Algebra.IsIntegral.of_finite k (X ⧸ m)
  have hbij : Function.Bijective (algebraMap k (X ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : k ≃+* (X ⧸ m) := RingEquiv.ofBijective (algebraMap k (X ⧸ m)) hbij
  let χ : X →ₐ[k] k :=
    { toRingHom := (e.symm : (X ⧸ m) →+* k).comp (Ideal.Quotient.mk m)
      commutes' := fun c => by
        show e.symm (Ideal.Quotient.mk m (algebraMap k X c)) = c
        rw [show Ideal.Quotient.mk m (algebraMap k X c) = algebraMap k (X ⧸ m) c from
          (IsScalarTower.algebraMap_apply k X (X ⧸ m) c).symm]
        exact e.symm_apply_apply c }
  refine h χ ?_
  show e.symm (Ideal.Quotient.mk m u) = 0
  rw [show Ideal.Quotient.mk m u = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hum, map_zero]

/-- Step (iii)+(iv) of the orbit argument, fused: for a non-unit `f`, the determinant of
the multiplication matrix of `ρ(f)` — the norm — is not a unit either, since the matrix
representation and the co-action both reflect units. -/
theorem not_isUnit_det_mulMatrix_coaction {ρ : B →ₐ[R] B ⊗[R] A} (hρ : IsCoaction ρ)
    {f : B} (hf : ¬ IsUnit f) :
    ¬ IsUnit (mulMatrix R A (ρ f)).det := by
  intro hdet
  exact hf (isUnit_of_isUnit_coaction R A hρ
    (isUnit_of_isUnit_mulMatrix R A ((Matrix.isUnit_iff_isUnit_det _).mpr hdet)))

omit [Module.Free R A] [Module.Finite R A] in
/-- **Compatibility of the base-changed co-action with the right inclusion**:
`coactionBaseChange` applied to `1 ⊗ b` is the image of `ρ b` under `includeRight ⊗ id` —
the bridge that lets a point of `B` be read off from a point of the base change. -/
theorem coactionBaseChange_one_tmul (ρ : B →ₐ[R] B ⊗[R] A) (C' : Type*) [CommRing C']
    [Algebra R C'] [Algebra (coinvariants ρ) C'] [IsScalarTower R (coinvariants ρ) C']
    (b : B) :
    coactionBaseChange R A ρ C' ((1 : C') ⊗ₜ[coinvariants ρ] b)
      = Algebra.TensorProduct.map
          ((Algebra.TensorProduct.includeRight :
            B →ₐ[coinvariants ρ] C' ⊗[coinvariants ρ] B).restrictScalars R)
          (AlgHom.id R A) (ρ b) := by
  rw [coactionBaseChange_tmul]
  induction ρ b with
  | zero => simp
  | tmul b₀ a =>
    rw [show (baseChangeAssoc R A ρ C').symm
        ((1 : C') ⊗ₜ[coinvariants ρ] (b₀ ⊗ₜ[R] a))
        = ((1 : C') ⊗ₜ[coinvariants ρ] b₀) ⊗ₜ[R] a from
      Algebra.TensorProduct.assoc_symm_tmul _ _ _ _ _ _]
    rfl
  | add z w ihz ihw =>
    rw [TensorProduct.tmul_add, map_add, map_add, ihz, ihw]

omit [Module.Free R A] [Module.Finite R A] in
/-- **The scalar leg is co-action-invariant**: `coactionBaseChange` sends `c ⊗ 1` to
`includeLeft (c ⊗ 1)`, since the scalars `C' ⊗ 1` carry the trivial co-action. -/
theorem coactionBaseChange_scalar_tmul (ρ : B →ₐ[R] B ⊗[R] A) (C' : Type*) [CommRing C']
    [Algebra R C'] [Algebra (coinvariants ρ) C'] [IsScalarTower R (coinvariants ρ) C']
    (c : C') :
    coactionBaseChange R A ρ C' (c ⊗ₜ[coinvariants ρ] (1 : B))
      = Algebra.TensorProduct.includeLeft (S := R) (c ⊗ₜ[coinvariants ρ] (1 : B)) := by
  rw [coactionBaseChange_tmul, map_one]
  rw [show ((1 : B ⊗[R] A)) = (1 : B) ⊗ₜ[R] (1 : A) from Algebra.TensorProduct.one_def]
  rw [show (baseChangeAssoc R A ρ C').symm
      (c ⊗ₜ[coinvariants ρ] ((1 : B) ⊗ₜ[R] (1 : A)))
      = (c ⊗ₜ[coinvariants ρ] (1 : B)) ⊗ₜ[R] (1 : A) from
    Algebra.TensorProduct.assoc_symm_tmul _ _ _ _ _ _]
  rfl

/-- **Step (iii) of the orbit argument (the norm is a co-invariant)**: the determinant of
the multiplication matrix of `ρ f` — the norm of `f` — is a co-invariant, being (a sign
times) the constant coefficient of the co-action characteristic polynomial
(`coactionCharpoly_coeff_mem`). -/
theorem det_mulMatrix_coaction_mem_coinvariants {B' : Type*} [CommRing B'] [Algebra R B']
    {ρ' : B' →ₐ[R] B' ⊗[R] A} (hρ' : IsCoaction ρ') (f : B') :
    (mulMatrix R A (ρ' f)).det ∈ coinvariants ρ' := by
  rw [Matrix.det_eq_sign_charpoly_coeff (mulMatrix R A (ρ' f))]
  exact mul_mem (pow_mem (neg_mem (one_mem _)) _)
    (coactionCharpoly_coeff_mem R A ρ' hρ' f 0)

/-- **Step (vi) of the orbit argument (the power-witness contradiction)**: a co-invariant
`g` of the base-changed co-action that some `k`-point `φ` sends to a nonzero value must be a
unit. Its `card`-th power lies in the image of `k`
(`pow_card_mem_range_algebraMap_of_mem_coinvariants`) and is nonzero, hence a unit, and one
factor of that power is `g` itself. -/
theorem isUnit_of_algHom_ne_zero_of_mem_coinvariants (ρ : B →ₐ[R] B ⊗[R] A)
    [Algebra (coinvariants ρ) k] [IsScalarTower R (coinvariants ρ) k] (hρ : IsCoaction ρ)
    (φ : (k ⊗[coinvariants ρ] B) →ₐ[k] k) {g : k ⊗[coinvariants ρ] B}
    (hgmem : g ∈ coinvariants (coactionBaseChange R A ρ k)) (hφg : φ g ≠ 0) :
    IsUnit g := by
  haveI : Nontrivial R := ⟨1, 0, fun h01 => one_ne_zero (α := k) (by
    rw [← map_one (algebraMap R k), h01, map_zero])⟩
  haveI : Nontrivial A := ⟨1, 0, fun h01 => one_ne_zero (α := R) (by
    have h2 := congrArg (Bialgebra.counitAlgHom R A) h01
    rwa [map_one, map_zero] at h2)⟩
  haveI : Nonempty (hopfBasisIndex R A) := (hopfBasis R A).index_nonempty
  obtain ⟨c, hc⟩ := pow_card_mem_range_algebraMap_of_mem_coinvariants R A ρ k hρ g hgmem
  have hcval : φ (g ^ Fintype.card (hopfBasisIndex R A)) = c := by
    rw [← hc, AlgHom.commutes, Algebra.algebraMap_self_apply]
  have hcne : c ≠ 0 := by
    rw [← hcval, map_pow]
    exact pow_ne_zero _ hφg
  have hgpow : IsUnit (g ^ Fintype.card (hopfBasisIndex R A)) := by
    rw [← hc]
    exact (isUnit_iff_ne_zero.mpr hcne).map (algebraMap k (k ⊗[coinvariants ρ] B))
  have hcard : Fintype.card (hopfBasisIndex R A) ≠ 0 := Fintype.card_ne_zero
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hcard
  rw [hn, pow_succ] at hgpow
  exact isUnit_of_mul_isUnit_right hgpow

/-- **The orbit theorem (Stacks 03BL(2), comodule form)**: over an algebraically closed
field `k`, two `k`-points of `B` agreeing on the co-invariants are connected by a
`k`-point of `B ⊗ A` through the groupoid legs `(ρ, includeLeft)`. -/
theorem exists_algHom_comp_eq [IsAlgClosed k] (ρ : B →ₐ[R] B ⊗[R] A) (hρ : IsCoaction ρ)
    (a₀ a₁ : B →ₐ[R] k) (hagree : ∀ x ∈ coinvariants ρ, a₀ x = a₁ x) :
    ∃ χ : (B ⊗[R] A) →ₐ[R] k,
      χ.comp ρ = a₀ ∧ χ.comp (Algebra.TensorProduct.includeLeft (S := R)) = a₁ := by
  classical
  -- make k a C-algebra through the common restriction
  letI : Algebra (coinvariants ρ) k :=
    ((a₁.comp (IsScalarTower.toAlgHom R (coinvariants ρ) B)).toRingHom).toAlgebra
  haveI : IsScalarTower R (coinvariants ρ) k := IsScalarTower.of_algebraMap_eq fun c => by
    show algebraMap R k c = a₁ (algebraMap R B c)
    rw [AlgHom.commutes]
  -- the lifted points of B_k := k ⊗[C] B
  let ā₁ : (k ⊗[coinvariants ρ] B) →ₐ[k] k :=
    Algebra.TensorProduct.lift (AlgHom.id k k)
      { toRingHom := a₁.toRingHom, commutes' := fun c => rfl }
      (fun _ _ => Commute.all _ _)
  let ā₀ : (k ⊗[coinvariants ρ] B) →ₐ[k] k :=
    Algebra.TensorProduct.lift (AlgHom.id k k)
      { toRingHom := a₀.toRingHom, commutes' := fun c => (hagree (c : B) c.2) }
      (fun _ _ => Commute.all _ _)
  have hā₁_tmul : ∀ (c : k) (b : B), ā₁ (c ⊗ₜ[coinvariants ρ] b) = c * a₁ b := fun c b =>
    Algebra.TensorProduct.lift_tmul _ _ _ _ _
  have hā₀_tmul : ∀ (c : k) (b : B), ā₀ (c ⊗ₜ[coinvariants ρ] b) = c * a₀ b := fun c b =>
    Algebra.TensorProduct.lift_tmul _ _ _ _ _
  -- the canonical comparison B ⊗ A → B_k ⊗ A and its compatibility with the co-actions
  let j : (B ⊗[R] A) →ₐ[R] (k ⊗[coinvariants ρ] B) ⊗[R] A :=
    Algebra.TensorProduct.map
      ((Algebra.TensorProduct.includeRight :
        B →ₐ[coinvariants ρ] k ⊗[coinvariants ρ] B).restrictScalars R)
      (AlgHom.id R A)
  have hj_coaction : ∀ b : B,
      j (ρ b) = coactionBaseChange R A ρ k ((1 : k) ⊗ₜ[coinvariants ρ] b) := fun b =>
    (coactionBaseChange_one_tmul R A ρ k b).symm
  -- reduce to producing a point upstairs
  by_contra hcon
  push Not at hcon
  -- any upstairs k-point over ā₁ whose ρ_k-restriction is ā₀ descends to a solution
  have hdescend : ∀ Χ : ((k ⊗[coinvariants ρ] B) ⊗[R] A) →ₐ[k] k,
      (∀ x, Χ (Algebra.TensorProduct.includeLeft (S := R) x) = ā₁ x) →
      (∀ x, Χ (coactionBaseChange R A ρ k x) = ā₀ x) → False := by
    intro Χ hΧι hΧρ
    refine hcon ((Χ.restrictScalars R).comp j) ?_ ?_
    · refine AlgHom.ext fun b => ?_
      show Χ (j (ρ b)) = a₀ b
      rw [hj_coaction b, hΧρ ((1 : k) ⊗ₜ[coinvariants ρ] b), hā₀_tmul, one_mul]
    · refine AlgHom.ext fun b => ?_
      show Χ (j (b ⊗ₜ[R] (1 : A))) = a₁ b
      rw [show j (b ⊗ₜ[R] (1 : A))
          = Algebra.TensorProduct.includeLeft (S := R)
              ((1 : k) ⊗ₜ[coinvariants ρ] b) from rfl,
        hΧι ((1 : k) ⊗ₜ[coinvariants ρ] b), hā₁_tmul, one_mul]
  -- the k-points of B_k ⊗ A over ā₁, with their ρ_k-restrictions upgraded to k-points
  have hρk_scalar : ∀ c : k, coactionBaseChange R A ρ k (c ⊗ₜ[coinvariants ρ] (1 : B))
      = Algebra.TensorProduct.includeLeft (S := R) (c ⊗ₜ[coinvariants ρ] (1 : B)) :=
    fun c => coactionBaseChange_scalar_tmul R A ρ k c
  -- the set of k-points over ā₁ is finite (via the R-linear finiteness + upgrade)
  set SR : Set (((k ⊗[coinvariants ρ] B) ⊗[R] A) →ₐ[R] k) :=
    {χ | χ.comp (Algebra.TensorProduct.includeLeft (S := R)) = ā₁.restrictScalars R}
    with hSR
  have hSRfin : SR.Finite := finite_setOf_comp_includeLeft_eq R A (ā₁.restrictScalars R)
  haveI : Finite SR := hSRfin.to_subtype
  -- a member of SR sends any left-inclusion scalar to that scalar
  have hSRscalar : ∀ (χ : SR) (c : k),
      (χ : ((k ⊗[coinvariants ρ] B) ⊗[R] A) →ₐ[R] k)
        (Algebra.TensorProduct.includeLeft (S := R) (c ⊗ₜ[coinvariants ρ] (1 : B))) = c := by
    intro χ c
    rw [show (χ : ((k ⊗[coinvariants ρ] B) ⊗[R] A) →ₐ[R] k)
        (Algebra.TensorProduct.includeLeft (S := R) (c ⊗ₜ[coinvariants ρ] (1 : B)))
        = (ā₁.restrictScalars R) (c ⊗ₜ[coinvariants ρ] (1 : B)) from
      AlgHom.congr_fun χ.2 _]
    show ā₁ (c ⊗ₜ[coinvariants ρ] (1 : B)) = c
    rw [hā₁_tmul, map_one, mul_one]
  -- upgrade the ρ_k-restriction of a member of SR to a k-point of B_k
  let upg : SR → ((k ⊗[coinvariants ρ] B) →ₐ[k] k) := fun χ =>
    { toRingHom := ((χ : ((k ⊗[coinvariants ρ] B) ⊗[R] A) →ₐ[R] k).comp
        (coactionBaseChange R A ρ k)).toRingHom
      commutes' := fun c => by
        show (χ : ((k ⊗[coinvariants ρ] B) ⊗[R] A) →ₐ[R] k)
          (coactionBaseChange R A ρ k (c ⊗ₜ[coinvariants ρ] (1 : B))) = c
        rw [hρk_scalar c]
        exact hSRscalar χ c }
  set T : Finset ((k ⊗[coinvariants ρ] B) →ₐ[k] k) :=
    (Set.finite_range upg).toFinset with hT
  -- ā₀ is not among the upgraded restrictions, else `hdescend` fires
  have hā₀T : ā₀ ∉ T := by
    rw [hT, Set.Finite.mem_toFinset]
    rintro ⟨χ, hχ⟩
    -- upgrade χ itself to a k-point upstairs and descend
    refine hdescend
      { toRingHom := (χ : ((k ⊗[coinvariants ρ] B) ⊗[R] A) →ₐ[R] k).toRingHom
        commutes' := fun c => by
          show (χ : ((k ⊗[coinvariants ρ] B) ⊗[R] A) →ₐ[R] k)
            (Algebra.TensorProduct.includeLeft (S := R)
              (c ⊗ₜ[coinvariants ρ] (1 : B))) = c
          exact hSRscalar χ c }
      (fun x => AlgHom.congr_fun χ.2 x) (fun x => ?_)
    exact AlgHom.congr_fun hχ x
  -- avoidance: an element of ker ā₀ outside every restricted kernel
  obtain ⟨ft, hft₀, hftT⟩ := exists_mem_ker_notMem_ker ā₀ T hā₀T
  -- (iii): the norm g of ρ_k(ft) is a co-invariant
  have hρk := isCoaction_coactionBaseChange R A ρ k hρ
  set g := (mulMatrix R A (coactionBaseChange R A ρ k ft)).det with hg
  have hgmem : g ∈ coinvariants (coactionBaseChange R A ρ k) := by
    rw [hg]
    exact det_mulMatrix_coaction_mem_coinvariants R A hρk ft
  -- (iv): g is not a unit
  have hftnu : ¬ IsUnit ft := fun hunit => by
    have := hunit.map ā₀
    rw [show ā₀ ft = 0 from hft₀] at this
    exact this.ne_zero rfl
  have hgnu : ¬ IsUnit g := not_isUnit_det_mulMatrix_coaction R A hρk hftnu
  -- (v): ā₁(g) ≠ 0
  have hā₁g : ā₁ g ≠ 0 := by
    have hmapdet : ā₁ g = (ā₁.toRingHom.mapMatrix
        (mulMatrix R A (coactionBaseChange R A ρ k ft))).det := by
      rw [hg]
      exact RingHom.map_det ā₁.toRingHom
        (mulMatrix R A (coactionBaseChange R A ρ k ft))
    have hmm : ā₁.toRingHom.mapMatrix (mulMatrix R A (coactionBaseChange R A ρ k ft))
        = mulMatrix R A ((Algebra.TensorProduct.map (ā₁.restrictScalars R)
            (AlgHom.id R A)) (coactionBaseChange R A ρ k ft)) := by
      rw [RingHom.mapMatrix_apply]
      exact (mulMatrix_map R A (ā₁.restrictScalars R) _).symm
    have hu : IsUnit ((Algebra.TensorProduct.map (ā₁.restrictScalars R)
        (AlgHom.id R A)) (coactionBaseChange R A ρ k ft)) := by
      refine isUnit_of_forall_algHom_ne_zero (k := k)
        (u := (Algebra.TensorProduct.map (ā₁.restrictScalars R) (AlgHom.id R A))
          (coactionBaseChange R A ρ k ft)) (fun ψ => ?_)
      have hmem : (ψ.restrictScalars R).comp (Algebra.TensorProduct.map
          (ā₁.restrictScalars R) (AlgHom.id R A)) ∈ SR := by
        rw [hSR]
        refine Set.mem_setOf.mpr (AlgHom.ext fun x => ?_)
        show ψ ((Algebra.TensorProduct.map (ā₁.restrictScalars R) (AlgHom.id R A))
          (x ⊗ₜ[R] (1 : A))) = ā₁ x
        rw [show (Algebra.TensorProduct.map (ā₁.restrictScalars R) (AlgHom.id R A))
            (x ⊗ₜ[R] (1 : A)) = ā₁ x ⊗ₜ[R] (1 : A) from by
          rw [Algebra.TensorProduct.map_tmul]; rfl]
        rw [show (ā₁ x ⊗ₜ[R] (1 : A) : k ⊗[R] A) = algebraMap k (k ⊗[R] A) (ā₁ x) from
          rfl, AlgHom.commutes, Algebra.algebraMap_self_apply]
      have hnotker := hftT (upg ⟨_, hmem⟩) (by
        rw [hT, Set.Finite.mem_toFinset]
        exact ⟨⟨_, hmem⟩, rfl⟩)
      rw [RingHom.mem_ker] at hnotker
      exact fun h0 => hnotker (by
        show (upg ⟨_, hmem⟩) ft = 0
        show ψ ((Algebra.TensorProduct.map (ā₁.restrictScalars R) (AlgHom.id R A))
          (coactionBaseChange R A ρ k ft)) = 0
        exact h0)
    rw [hmapdet, hmm]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp (hu.map (mulMatrixHom R A))).ne_zero
  -- (vi): the power witness forces g to be a unit — contradiction with (iv)
  exact hgnu (isUnit_of_algHom_ne_zero_of_mem_coinvariants R A ρ hρ ā₁ hgmem hā₁g)

/-- **GAP-6 (semi-locality, Stacks 03BM's semi-local step)**: when the co-invariants form
a local ring, `B` has only finitely many maximal ideals. Each maximal ideal is the kernel
of a point into the algebraic closure of the residue field (`IsAlgClosed.lift` on the
integral residue extension), all such points agree on the co-invariants (their
restriction is the canonical residue map), so the orbit theorem confines them — hence the
maximal ideals — to the finite fibre over any fixed one. -/
theorem finite_setOf_isMaximal_of_isLocalRing (ρ : B →ₐ[R] B ⊗[R] A) (hρ : IsCoaction ρ)
    [IsLocalRing (coinvariants ρ)] :
    {n : Ideal B | n.IsMaximal}.Finite := by
  classical
  haveI : Algebra.IsIntegral (coinvariants ρ) B :=
    isIntegral_algebra_coinvariants R A ρ hρ
  set κ := IsLocalRing.ResidueField (coinvariants ρ) with hκdef
  -- the ambient algebraically closed field, as an R-algebra through the residue map
  letI : Algebra R (AlgebraicClosure κ) :=
    ((algebraMap κ (AlgebraicClosure κ)).comp
      ((IsLocalRing.residue (coinvariants ρ)).comp
        (algebraMap R (coinvariants ρ)))).toAlgebra
  -- pointify each maximal ideal
  have hpoint : ∀ n : Ideal B, n.IsMaximal →
      ∃ χ : B →ₐ[R] AlgebraicClosure κ,
        RingHom.ker χ.toRingHom = n ∧
        ∀ (x : B) (hx : x ∈ coinvariants ρ), χ x
          = algebraMap κ (AlgebraicClosure κ)
              (IsLocalRing.residue (coinvariants ρ) ⟨x, hx⟩) := by
    intro n hn
    haveI := hn
    have hcomap : IsLocalRing.maximalIdeal (coinvariants ρ)
        = Ideal.comap (algebraMap (coinvariants ρ) B) n := by
      haveI := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
        (R := coinvariants ρ) (S := B) n
      exact (IsLocalRing.eq_maximalIdeal inferInstance).symm
    let q : κ →+* B ⧸ n :=
      Ideal.quotientMap n (algebraMap (coinvariants ρ) B) (le_of_eq hcomap)
    letI : Algebra κ (B ⧸ n) := q.toAlgebra
    haveI hqint : Algebra.IsIntegral κ (B ⧸ n) := by
      constructor
      intro x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨p, hpm, hpev⟩ := isIntegral_coinvariants R A ρ hρ b
      refine ⟨p.map (IsLocalRing.residue (coinvariants ρ)), hpm.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      rw [show (algebraMap κ (B ⧸ n)).comp (IsLocalRing.residue (coinvariants ρ))
          = (Ideal.Quotient.mk n).comp (algebraMap (coinvariants ρ) B) from
        Ideal.quotientMap_comp_mk (le_of_eq hcomap)]
      rw [← Polynomial.hom_eval₂, hpev, map_zero]
    haveI : Algebra.IsAlgebraic κ (B ⧸ n) := Algebra.IsIntegral.isAlgebraic
    let ε : (B ⧸ n) →ₐ[κ] AlgebraicClosure κ := IsAlgClosed.lift
    -- the point: ε after the quotient, R-linear through the residue tower
    refine ⟨{ toRingHom := (ε.toRingHom.comp (Ideal.Quotient.mk n))
              commutes' := fun r => ?_ }, ?_, ?_⟩
    · show ε (Ideal.Quotient.mk n (algebraMap R B r)) = _
      rw [show algebraMap R B r
          = algebraMap (coinvariants ρ) B (algebraMap R (coinvariants ρ) r) from
        (IsScalarTower.algebraMap_apply R (coinvariants ρ) B r)]
      rw [show Ideal.Quotient.mk n
            (algebraMap (coinvariants ρ) B (algebraMap R (coinvariants ρ) r))
          = q (IsLocalRing.residue (coinvariants ρ) (algebraMap R (coinvariants ρ) r))
        from (RingHom.congr_fun (Ideal.quotientMap_comp_mk (le_of_eq hcomap)) _).symm]
      rw [show q (IsLocalRing.residue (coinvariants ρ) (algebraMap R (coinvariants ρ) r))
          = algebraMap κ (B ⧸ n)
              (IsLocalRing.residue (coinvariants ρ) (algebraMap R (coinvariants ρ) r))
        from rfl]
      rw [AlgHom.commutes]
      rfl
    · -- the kernel: contains n, is proper, and n is maximal
      show RingHom.ker (ε.toRingHom.comp (Ideal.Quotient.mk n)) = n
      have hle : n ≤ RingHom.ker (ε.toRingHom.comp (Ideal.Quotient.mk n)) := by
        intro b hb
        rw [RingHom.mem_ker, RingHom.comp_apply,
          Ideal.Quotient.eq_zero_iff_mem.mpr hb, map_zero]
      exact (hn.eq_of_le (RingHom.ker_ne_top _) hle).symm
    · -- the co-invariant restriction is canonical
      intro x hx
      show ε (Ideal.Quotient.mk n x) = _
      have hstep : Ideal.Quotient.mk n x
          = algebraMap κ (B ⧸ n) (IsLocalRing.residue (coinvariants ρ) ⟨x, hx⟩) :=
        (RingHom.congr_fun (Ideal.quotientMap_comp_mk (le_of_eq hcomap))
          (⟨x, hx⟩ : coinvariants ρ)).symm
      rw [hstep, AlgHom.commutes]
  -- if there is no maximal ideal, done; else fix one and confine the rest
  by_cases hex : ∃ n₀ : Ideal B, n₀.IsMaximal
  · obtain ⟨n₀, hn₀⟩ := hex
    obtain ⟨χ₀, hχ₀ker, hχ₀c⟩ := hpoint n₀ hn₀
    -- every maximal's point is confined: it factors through the finite fibre over χ₀
    have hfin := finite_setOf_comp_includeLeft_eq R A (k := AlgebraicClosure κ) χ₀
    -- the map n ↦ the connecting point Χ_n (choice), injective onto the fibre
    have hconn : ∀ n : {n : Ideal B | n.IsMaximal},
        ∃ Χ : (B ⊗[R] A) →ₐ[R] AlgebraicClosure κ,
          Χ.comp (Algebra.TensorProduct.includeLeft (S := R)) = χ₀ ∧
          RingHom.ker (Χ.comp ρ).toRingHom = (n : Ideal B) := by
      rintro ⟨n, hn⟩
      obtain ⟨χ, hχker, hχc⟩ := hpoint n hn
      obtain ⟨Χ, hΧρ, hΧι⟩ := exists_algHom_comp_eq R A ρ hρ χ χ₀ (fun x hx => by
        rw [hχc x hx, hχ₀c x hx])
      refine ⟨Χ, hΧι, ?_⟩
      rw [hΧρ]
      exact hχker
    choose Χmap hΧι hΧker using hconn
    -- injectivity: the kernel of Χ∘ρ recovers n
    have hinj : Function.Injective Χmap := by
      intro n₁ n₂ h
      refine Subtype.ext ?_
      rw [← hΧker n₁, ← hΧker n₂, h]
    -- Χmap lands in the finite fibre set over χ₀
    have hrange : Set.range Χmap ⊆ {χ | χ.comp
        (Algebra.TensorProduct.includeLeft (S := R)) = χ₀} := by
      rintro - ⟨n, rfl⟩
      exact hΧι n
    haveI : Finite {χ : (B ⊗[R] A) →ₐ[R] AlgebraicClosure κ | χ.comp
        (Algebra.TensorProduct.includeLeft (S := R)) = χ₀} := hfin.to_subtype
    haveI : Finite (Set.range Χmap) := Set.Finite.to_subtype
      (Set.Finite.subset hfin hrange)
    haveI : Finite {n : Ideal B | n.IsMaximal} :=
      Finite.of_injective
        (fun n => (⟨Χmap n, ⟨n, rfl⟩⟩ : Set.range Χmap))
        (fun a b h => hinj (congrArg Subtype.val h))
    exact Set.toFinite _
  · push Not at hex
    refine Set.Finite.subset (Set.finite_empty) (fun n hn => (hex n hn).elim)

/-- Over a local co-invariants base, every maximal ideal of `B` lies over the maximal
ideal: `m·B ≤ n`. (Contraction is maximal by integrality, hence equals `m`.) -/
theorem maximalIdeal_map_le_of_isMaximal (ρ : B →ₐ[R] B ⊗[R] A) (hρ : IsCoaction ρ)
    [IsLocalRing (coinvariants ρ)] (n : Ideal B) (hn : n.IsMaximal) :
    (IsLocalRing.maximalIdeal (coinvariants ρ)).map
      (algebraMap (coinvariants ρ) B) ≤ n := by
  haveI : Algebra.IsIntegral (coinvariants ρ) B :=
    isIntegral_algebra_coinvariants R A ρ hρ
  haveI := hn
  haveI := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
    (R := coinvariants ρ) (S := B) n
  rw [Ideal.map_le_iff_le_comap, IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := coinvariants ρ) (S := B) n)]

end Orbit

end ModularCurves
