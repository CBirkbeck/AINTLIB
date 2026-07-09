import ModularCurves.ForMathlib.CoactionCharpoly
import ModularCurves.ForMathlib.CoinvariantsBaseChange
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IsAlgClosed.Basic
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

end Orbit

end ModularCurves
