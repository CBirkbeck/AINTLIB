module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.LinearAlgebra.Trace
public import BernoulliRegular.GaussSum.Basic

/-!
# Finite-Fourier sign invariants for quadratic Gauss sums

This file contains the trace and character-cancellation side of the
finite-Fourier sign-invariant package.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

open scoped BigOperators ComplexConjugate

section SignInvariant

variable (p : ℕ) [hp : Fact p.Prime]

/-- The discrete Fourier transform of the standard basis vector at `x` is the
`x`-th Fourier kernel row. -/
theorem dft_basisFun_apply (x k : ZMod p) :
    ZMod.dft (Pi.basisFun ℂ (ZMod p) x) k =
      ZMod.stdAddChar (N := p) (-(x * k)) := by
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul, Pi.basisFun_apply, Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ x (fun y : ZMod p => ZMod.stdAddChar (N := p) (-(y * k)))]
  simp

/-- The DFT sends the delta function at `0` to the constant-one function. -/
theorem dft_deltaZero_eq_constOne :
    ZMod.dft (Pi.basisFun ℂ (ZMod p) (0 : ZMod p)) = fun _ : ZMod p => (1 : ℂ) := by
  ext k
  rw [dft_basisFun_apply (p := p) (x := (0 : ZMod p)) (k := k)]
  simp

/-- The DFT of the constant-one function is concentrated at `0`. -/
theorem dft_constOne (k : ZMod p) :
    ZMod.dft (fun _ : ZMod p => (1 : ℂ)) k = if k = 0 then p else 0 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  by_cases hk : k = 0
  · subst hk
    rw [ZMod.dft_apply_zero]
    simp
  · rw [ZMod.dft_apply, if_neg hk]
    have hne : ((ZMod.stdAddChar : AddChar (ZMod p) ℂ).mulShift (-k)) ≠ 1 := by
      intro hshift
      have heval : (ZMod.stdAddChar (N := p)) (-k) = 1 := by
        simpa [AddChar.mulShift_apply] using
          congrArg (fun ψ : AddChar (ZMod p) ℂ => ψ 1) hshift
      have hzero : (ZMod.stdAddChar (N := p)) (0 : ZMod p) = 1 := AddChar.map_zero_eq_one _
      have hkzero : (-k : ZMod p) = 0 := ZMod.injective_stdAddChar (heval.trans hzero.symm)
      exact hk (by simpa using hkzero)
    have hsum : ∑ j : ZMod p, ((ZMod.stdAddChar : AddChar (ZMod p) ℂ).mulShift (-k)) j = 0 :=
      AddChar.sum_eq_zero_of_ne_one hne
    simpa [AddChar.mulShift_apply, mul_comm, mul_left_comm, mul_assoc] using hsum

/-- Equivalently, the DFT sends the constant-one function to `p • δ₀`. -/
theorem dft_constOne_eq_prime_smul_deltaZero :
    ZMod.dft (fun _ : ZMod p => (1 : ℂ)) =
      (p : ℂ) • Pi.basisFun ℂ (ZMod p) (0 : ZMod p) := by
  ext k
  by_cases hk : k = 0
  · subst hk
    simp [dft_constOne (p := p), Pi.basisFun_apply]
  · simp [dft_constOne (p := p), hk, Pi.basisFun_apply]

/-- The DFT interchanges the `δ₀` and constant-one lines, so this `2 × 2`
block has trace `0`. -/
theorem dft_constOne_deltaZero_offDiagonal :
    ZMod.dft (Pi.basisFun ℂ (ZMod p) (0 : ZMod p)) =
        (1 : ℂ) • (fun _ : ZMod p => (1 : ℂ)) ∧
      ZMod.dft (fun _ : ZMod p => (1 : ℂ)) =
        (p : ℂ) • Pi.basisFun ℂ (ZMod p) (0 : ZMod p) := by
  constructor
  · simpa using dft_deltaZero_eq_constOne (p := p)
  · exact dft_constOne_eq_prime_smul_deltaZero (p := p)

/-- The diagonal sum of the `ZMod` Fourier kernel. This is the finite-Fourier
sign-detecting invariant used in the `T023d1g` plan. -/
noncomputable def quadraticDftTraceInvariant : ℂ :=
  ∑ x : ZMod p, ZMod.stdAddChar (N := p) (-(x ^ 2))

/-- Unfolding the invariant just gives the diagonal kernel sum. -/
theorem quadraticDftTraceInvariant_def :
    quadraticDftTraceInvariant p =
      ∑ x : ZMod p, ZMod.stdAddChar (N := p) (-(x ^ 2)) := by
  rfl

/-- The sign invariant is literally the trace of `ZMod.dft` on the standard
basis of the function space `ZMod p → ℂ`. -/
theorem quadraticDftTraceInvariant_eq_trace_dft :
    quadraticDftTraceInvariant p =
      LinearMap.trace ℂ (ZMod p → ℂ)
        ((ZMod.dft : (ZMod p → ℂ) ≃ₗ[ℂ] (ZMod p → ℂ)).toLinearMap) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace
    (R := ℂ)
    (b := Pi.basisFun ℂ (ZMod p))
    (f := ((ZMod.dft : (ZMod p → ℂ) ≃ₗ[ℂ] (ZMod p → ℂ)).toLinearMap))]
  rw [Matrix.trace, quadraticDftTraceInvariant_def]
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basisFun_repr]
  change ZMod.stdAddChar (N := p) (-(x ^ 2)) = ZMod.dft (Pi.basisFun ℂ (ZMod p) x) x
  rw [dft_basisFun_apply]
  simp [pow_two]

/-- Conjugating the standard additive character negates its input. -/
theorem stdAddChar_neg_eq_conj (a : ZMod p) :
    ZMod.stdAddChar (N := p) (-a) = conj (ZMod.stdAddChar (N := p) a) := by
  symm
  rw [ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv,
    ← ZMod.stdAddChar_apply]

/-- The sign invariant is the conjugate quadratic Gauss sum. -/
theorem quadraticDftTraceInvariant_eq_conj_gaussSum
    (hp₂ : p ≠ 2) :
    quadraticDftTraceInvariant p =
      conj (gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p))) := by
  calc
    quadraticDftTraceInvariant p =
        ∑ x : ZMod p, conj (ZMod.stdAddChar (N := p) (x ^ 2)) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          simpa using stdAddChar_neg_eq_conj (p := p) (a := x ^ 2)
    _ = conj (∑ x : ZMod p, ZMod.stdAddChar (N := p) (x ^ 2)) := by
          symm
          exact map_sum conj (fun x : ZMod p => ZMod.stdAddChar (N := p) (x ^ 2)) Finset.univ
    _ = conj (gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p))) := by
          rw [gaussSum_quadraticCharComplex_eq_squareExponentialSum (p := p) hp₂]

/-- Any nontrivial Dirichlet character is sent by the DFT to a scalar multiple
of its inverse character. -/
theorem dft_eq_scalar_smul_inv_character {χ : DirichletCharacter ℂ p}
    (hχ : χ ≠ 1) :
    ZMod.dft χ =
      (χ⁻¹ (-1) * gaussSum χ (ZMod.stdAddChar (N := p))) •
        (((χ⁻¹ : DirichletCharacter ℂ p) : ZMod p → ℂ)) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hprim : χ.IsPrimitive := DirichletCharacter.isPrimitive_of_ne_one (p := p) hχ
  ext k
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    ZMod.dft χ k = χ⁻¹ (-k) * gaussSum χ (ZMod.stdAddChar (N := p)) :=
      DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum
        (χ := χ) hprim k
    _ = (χ⁻¹ (-1) * gaussSum χ (ZMod.stdAddChar (N := p))) * χ⁻¹ k := by
      rw [show χ⁻¹ (-k) = χ⁻¹ (-1) * χ⁻¹ k by
        calc
          χ⁻¹ (-k) = χ⁻¹ ((-1 : ZMod p) * k) := by congr; ring
          _ = χ⁻¹ (-1) * χ⁻¹ k := by rw [map_mul]]
      ring

/-- Hence every nontrivial character pair `(χ, χ⁻¹)` is an off-diagonal DFT
block; when `χ ≠ χ⁻¹`, this is the local cancellation mechanism behind
`T023d1g1a`. -/
theorem dft_nontrivial_character_pair_offDiagonal {χ : DirichletCharacter ℂ p}
    (hχ : χ ≠ 1) :
    ∃ a b : ℂ,
  ZMod.dft (χ : ZMod p → ℂ) = a • (((χ⁻¹ : DirichletCharacter ℂ p) : ZMod p → ℂ)) ∧
  ZMod.dft (((χ⁻¹ : DirichletCharacter ℂ p) : ZMod p → ℂ)) = b • (χ : ZMod p → ℂ) := by
  refine ⟨χ⁻¹ (-1) * gaussSum χ (ZMod.stdAddChar (N := p)),
    χ (-1) * gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)), ?_, ?_⟩
  · exact dft_eq_scalar_smul_inv_character (p := p) hχ
  · have hχinv : χ⁻¹ ≠ (1 : DirichletCharacter ℂ p) := by
      intro h
      apply hχ
      calc
        χ = (χ⁻¹)⁻¹ := by simp
        _ = (1 : DirichletCharacter ℂ p)⁻¹ := by rw [h]
        _ = 1 := by simp
    simpa using dft_eq_scalar_smul_inv_character (p := p) (χ := χ⁻¹) hχinv

/-- The candidate `2 × 2` block attached to a character pair `(χ, χ⁻¹)`. -/
noncomputable def characterPairSubmodule (χ : DirichletCharacter ℂ p) :
    Submodule ℂ (ZMod p → ℂ) :=
  Submodule.span ℂ
    (Set.range
      ![(χ : ZMod p → ℂ), (((χ⁻¹ : DirichletCharacter ℂ p) : ZMod p → ℂ))])

omit hp in
theorem character_mem_characterPairSubmodule (χ : DirichletCharacter ℂ p) :
    (χ : ZMod p → ℂ) ∈ characterPairSubmodule (p := p) χ := by
  apply Submodule.subset_span
  refine ⟨0, ?_⟩
  simp

omit hp in
theorem invCharacter_mem_characterPairSubmodule (χ : DirichletCharacter ℂ p) :
    (((χ⁻¹ : DirichletCharacter ℂ p) : ZMod p → ℂ)) ∈ characterPairSubmodule (p := p) χ := by
  apply Submodule.subset_span
  refine ⟨1, ?_⟩
  simp

/-- A character and its inverse span a genuine `2`-dimensional block unless the
character is self-dual. -/
theorem character_inv_linearIndependent {χ : DirichletCharacter ℂ p}
    (hχself : χ ≠ χ⁻¹) :
    LinearIndependent ℂ
      ![(χ : ZMod p → ℂ), (((χ⁻¹ : DirichletCharacter ℂ p) : ZMod p → ℂ))] := by
  have hχne0 : (χ : ZMod p → ℂ) ≠ 0 := by
    intro hzero
    have h1 : (1 : ℂ) = 0 := by
      simpa using congrFun hzero (1 : ZMod p)
    exact one_ne_zero h1
  rw [LinearIndependent.pair_iff' hχne0]
  intro a ha
  have ha1 : a = 1 := by
    have h1 := congrFun ha (1 : ZMod p)
    simpa [Pi.smul_apply] using h1
  apply hχself
  ext x
  have hx := congrFun ha x
  simpa [Pi.smul_apply, ha1] using hx

/-- The DFT preserves the span of a nontrivial character and its inverse. -/
theorem dft_maps_characterPairSubmodule {χ : DirichletCharacter ℂ p}
    (hχ : χ ≠ 1) {f : ZMod p → ℂ}
    (hf : f ∈ characterPairSubmodule (p := p) χ) :
    ZMod.dft f ∈ characterPairSubmodule (p := p) χ := by
  rcases dft_nontrivial_character_pair_offDiagonal (p := p) (χ := χ) hχ with ⟨a, b, ha, hb⟩
  refine Submodule.span_induction
    (p := fun g _ => ZMod.dft g ∈ characterPairSubmodule (p := p) χ) ?_ ?_ ?_ ?_ hf
  · intro g hg
    rcases hg with ⟨i, rfl⟩
    fin_cases i
    · simpa [ha] using
        Submodule.smul_mem (characterPairSubmodule (p := p) χ) a
          (invCharacter_mem_characterPairSubmodule (p := p) χ)
    · simpa [hb] using
        Submodule.smul_mem (characterPairSubmodule (p := p) χ) b
          (character_mem_characterPairSubmodule (p := p) χ)
  · simp
  · intro x y hx hy hxmem hymem
    simpa using (characterPairSubmodule (p := p) χ).add_mem hxmem hymem
  · intro c g hg hgmem
    simpa using (characterPairSubmodule (p := p) χ).smul_mem c hgmem

/-- On a non-self-dual character pair, the restricted DFT block has trace `0`. -/
theorem trace_restrict_characterPairSubmodule_eq_zero {χ : DirichletCharacter ℂ p}
    (hχ : χ ≠ 1) (hχself : χ ≠ χ⁻¹) :
    LinearMap.trace ℂ (characterPairSubmodule (p := p) χ)
      (((ZMod.dft : (ZMod p → ℂ) ≃ₗ[ℂ] (ZMod p → ℂ)).toLinearMap).restrict
        (fun _ hf => dft_maps_characterPairSubmodule (p := p) (χ := χ) hχ hf)) = 0 := by
  classical
  let pairBasis : Module.Basis (Fin 2) ℂ (characterPairSubmodule (p := p) χ) :=
    Module.Basis.span
      (R := ℂ)
      (v := ![(χ : ZMod p → ℂ), (((χ⁻¹ : DirichletCharacter ℂ p) : ZMod p → ℂ))])
      (character_inv_linearIndependent (p := p) (χ := χ) hχself)
  let dftPair : characterPairSubmodule (p := p) χ →ₗ[ℂ] characterPairSubmodule (p := p) χ :=
    ((ZMod.dft : (ZMod p → ℂ) ≃ₗ[ℂ] (ZMod p → ℂ)).toLinearMap).restrict
      (fun _ hf => dft_maps_characterPairSubmodule (p := p) (χ := χ) hχ hf)
  change LinearMap.trace ℂ (characterPairSubmodule (p := p) χ) dftPair = 0
  rcases dft_nontrivial_character_pair_offDiagonal (p := p) (χ := χ) hχ with ⟨a, b, ha, hb⟩
  have hpair0 :
      (((pairBasis (0 : Fin 2) : characterPairSubmodule (p := p) χ) : ZMod p → ℂ)) =
        (χ : ZMod p → ℂ) := by
    change
      (((Module.Basis.span
        (R := ℂ)
        (v := ![(χ : ZMod p → ℂ), (((χ⁻¹ : DirichletCharacter ℂ p) : ZMod p → ℂ))])
        (character_inv_linearIndependent (p := p) (χ := χ) hχself) (0 : Fin 2) :
          characterPairSubmodule (p := p) χ) : ZMod p → ℂ)) =
        ![(χ : ZMod p → ℂ), (((χ⁻¹ : DirichletCharacter ℂ p) : ZMod p → ℂ))] (0 : Fin 2)
    exact Module.Basis.coe_span_apply
      (R := ℂ)
      (v := ![(χ : ZMod p → ℂ), (((χ⁻¹ : DirichletCharacter ℂ p) : ZMod p → ℂ))])
      (hli := character_inv_linearIndependent (p := p) (χ := χ) hχself)
      (i := (0 : Fin 2))
  have hpair1 :
      (((pairBasis (1 : Fin 2) : characterPairSubmodule (p := p) χ) : ZMod p → ℂ)) =
        (((χ⁻¹ : DirichletCharacter ℂ p) : ZMod p → ℂ)) := by
    change
      (((Module.Basis.span
        (R := ℂ)
        (v := ![(χ : ZMod p → ℂ), (((χ⁻¹ : DirichletCharacter ℂ p) : ZMod p → ℂ))])
        (character_inv_linearIndependent (p := p) (χ := χ) hχself) (1 : Fin 2) :
          characterPairSubmodule (p := p) χ) : ZMod p → ℂ)) =
        ![(χ : ZMod p → ℂ), (((χ⁻¹ : DirichletCharacter ℂ p) : ZMod p → ℂ))] (1 : Fin 2)
    exact Module.Basis.coe_span_apply
      (R := ℂ)
      (v := ![(χ : ZMod p → ℂ), (((χ⁻¹ : DirichletCharacter ℂ p) : ZMod p → ℂ))])
      (hli := character_inv_linearIndependent (p := p) (χ := χ) hχself)
      (i := (1 : Fin 2))
  have hB0 : dftPair (pairBasis (0 : Fin 2)) = a • pairBasis (1 : Fin 2) := by
    ext x
    change
      ZMod.dft (((pairBasis (0 : Fin 2) : characterPairSubmodule (p := p) χ) : ZMod p → ℂ)) x =
        a * (((pairBasis (1 : Fin 2) : characterPairSubmodule (p := p) χ) : ZMod p → ℂ)) x
    rw [hpair0, hpair1]
    exact congrFun ha x
  have hB1 : dftPair (pairBasis (1 : Fin 2)) = b • pairBasis (0 : Fin 2) := by
    ext x
    change
      ZMod.dft (((pairBasis (1 : Fin 2) : characterPairSubmodule (p := p) χ) : ZMod p → ℂ)) x =
        b * (((pairBasis (0 : Fin 2) : characterPairSubmodule (p := p) χ) : ZMod p → ℂ)) x
    rw [hpair0, hpair1]
    exact congrFun hb x
  calc
    LinearMap.trace ℂ (characterPairSubmodule (p := p) χ) dftPair =
        Matrix.trace (LinearMap.toMatrix pairBasis pairBasis dftPair) := by
          rw [LinearMap.trace_eq_matrix_trace (R := ℂ) (b := pairBasis) (f := dftPair)]
    _ = Matrix.diag (LinearMap.toMatrix pairBasis pairBasis dftPair) (0 : Fin 2) +
          Matrix.diag (LinearMap.toMatrix pairBasis pairBasis dftPair) (1 : Fin 2) := by
          rw [Matrix.trace, Fin.sum_univ_two]
    _ = (LinearMap.toMatrix pairBasis pairBasis dftPair) (0 : Fin 2) (0 : Fin 2) +
          (LinearMap.toMatrix pairBasis pairBasis dftPair) (1 : Fin 2) (1 : Fin 2) := by
          simp [Matrix.diag_apply]
    _ = 0 + 0 := by
          congr 1
          · rw [LinearMap.toMatrix_apply, hB0]
            simp [pairBasis]
          · rw [LinearMap.toMatrix_apply, hB1]
            simp [pairBasis]
    _ = 0 := by simp

/-- A chosen multiplicative equivalence between complex-valued Dirichlet
characters mod `p` and the unit group `(ZMod p)ˣ`. -/
noncomputable def complexCharacterMulEquivUnits : DirichletCharacter ℂ p ≃* (ZMod p)ˣ := by
  letI : NeZero p := ⟨hp.out.ne_zero⟩
  exact (MulChar.mulEquiv_units (ZMod p) ℂ).some

omit hp in
/-- A self-inverse character squares to the trivial character. -/
theorem selfInverse_character_sq_eq_one {χ : DirichletCharacter ℂ p}
    (hχself : χ = χ⁻¹) : χ ^ 2 = 1 := by
  simpa [pow_two] using congrArg (fun ψ : DirichletCharacter ℂ p => ψ * χ) hχself

/-- Under the chosen unit-group equivalence, a self-inverse character maps to
an element of `(ZMod p)ˣ` whose square is `1`. -/
theorem selfInverse_character_image_sq_eq_one {χ : DirichletCharacter ℂ p}
    (hχself : χ = χ⁻¹) :
    (((complexCharacterMulEquivUnits (p := p) χ : (ZMod p)ˣ) : ZMod p) ^ 2) = 1 := by
  have hsq_units : (complexCharacterMulEquivUnits (p := p) χ : (ZMod p)ˣ) ^ 2 = 1 := by
    rw [← map_pow]
    simp [selfInverse_character_sq_eq_one (p := p) (χ := χ) hχself]
  simpa [Units.val_pow_eq_pow_val] using
    congrArg (fun u : (ZMod p)ˣ => ((u : ZMod p))) hsq_units

/-- Hence a self-inverse character maps to `1` or `-1` in `ZMod p`. -/
theorem selfInverse_character_image_eq_one_or_neg_one {χ : DirichletCharacter ℂ p}
    (hχself : χ = χ⁻¹) :
    ((complexCharacterMulEquivUnits (p := p) χ : (ZMod p)ˣ) : ZMod p) = 1 ∨
      ((complexCharacterMulEquivUnits (p := p) χ : (ZMod p)ˣ) : ZMod p) = -1 :=
  sq_eq_one_iff.mp <|
    selfInverse_character_image_sq_eq_one (p := p) (χ := χ) hχself

/-- Repackaging the previous lemma back in the unit group. -/
theorem selfInverse_character_image_units_eq_one_or_neg_one {χ : DirichletCharacter ℂ p}
    (hχself : χ = χ⁻¹) :
    complexCharacterMulEquivUnits (p := p) χ = 1 ∨
      complexCharacterMulEquivUnits (p := p) χ = (-1 : (ZMod p)ˣ) := by
  rcases selfInverse_character_image_eq_one_or_neg_one (p := p) (χ := χ) hχself with hχ | hχ
  · left
    apply Units.ext
    simpa using hχ
  · right
    apply Units.ext
    simpa using hχ

/-- The hard bridge for `T023d1g1a3`: under the chosen equivalence, the
quadratic complex Dirichlet character corresponds to the unique nontrivial
order-`2` unit `-1`. -/
theorem complexCharacterMulEquivUnits_quadraticCharComplex (hp₂ : p ≠ 2) :
    complexCharacterMulEquivUnits (p := p) (quadraticCharComplex p) = (-1 : (ZMod p)ˣ) := by
  rcases selfInverse_character_image_units_eq_one_or_neg_one
      (p := p) (χ := quadraticCharComplex p) (quadraticCharComplex_inv (p := p)).symm with hχ | hχ
  · exfalso
    apply quadraticCharComplex_ne_one (p := p) hp₂
    apply (complexCharacterMulEquivUnits (p := p)).injective
    simpa using hχ
  · exact hχ

/-- A self-inverse complex Dirichlet character is either trivial or quadratic. -/
theorem selfInverse_character_eq_one_or_quadratic (hp₂ : p ≠ 2)
    {χ : DirichletCharacter ℂ p} (hχself : χ = χ⁻¹) :
    χ = 1 ∨ χ = quadraticCharComplex p := by
  rcases selfInverse_character_image_units_eq_one_or_neg_one (p := p) (χ := χ) hχself with hχ | hχ
  · left
    apply (complexCharacterMulEquivUnits (p := p)).injective
    simpa using hχ
  · right
    apply (complexCharacterMulEquivUnits (p := p)).injective
    calc
      complexCharacterMulEquivUnits (p := p) χ = (-1 : (ZMod p)ˣ) := hχ
      _ = complexCharacterMulEquivUnits (p := p) (quadraticCharComplex p) := by
            symm
            exact complexCharacterMulEquivUnits_quadraticCharComplex (p := p) hp₂

/-- The only nontrivial self-inverse complex Dirichlet character mod `p` is the
quadratic character. -/
theorem nontrivial_selfInverse_character_eq_quadratic (hp₂ : p ≠ 2)
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) (hχself : χ = χ⁻¹) :
    χ = quadraticCharComplex p := by
  rcases selfInverse_character_eq_one_or_quadratic (p := p) hp₂ hχself with hχ1 | hχquad
  · exact (hχ hχ1).elim
  · exact hχquad

/-- Packaged output of the `T023d1g1a` cancellation step: once the trivial
`δ₀/1` block and all non-self-dual character pairs are shown to contribute zero
to the Fourier trace, the quadratic line is the only surviving term. This
identity is already recoverable from the phase package in `T023d1e`. -/
theorem quadraticDftTraceInvariant_nonquadratic_contributions_cancel
    (hp₂ : p ≠ 2) :
    quadraticDftTraceInvariant p =
      quadraticCharComplex p (-1) *
        gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p)) := by
  rw [quadraticDftTraceInvariant_eq_conj_gaussSum (p := p) hp₂,
    conj_gaussSum_quadraticCharComplex_eq_eval_neg_one_mul (p := p) hp₂]

/-- The surviving quadratic trace contribution can be rewritten using the
quadratic exponential sum isolated in `T023d1e`. -/
theorem quadraticDftTraceInvariant_eq_eval_neg_one_mul_squareExponentialSum
    (hp₂ : p ≠ 2) :
    quadraticDftTraceInvariant p =
      quadraticCharComplex p (-1) *
        ∑ x : ZMod p, ZMod.stdAddChar (N := p) (x ^ 2) := by
  rw [quadraticDftTraceInvariant_nonquadratic_contributions_cancel (p := p) hp₂,
    gaussSum_quadraticCharComplex_eq_squareExponentialSum (p := p) hp₂]

/-- If `p ≡ 1 (mod 4)`, the sign-detecting trace invariant is the quadratic
Gauss sum itself. -/
theorem quadraticDftTraceInvariant_eq_gaussSum_of_mod_four_eq_one
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 1) :
    quadraticDftTraceInvariant p =
      gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p)) := by
  rw [quadraticDftTraceInvariant_nonquadratic_contributions_cancel (p := p) hp₂,
    quadraticCharComplex_eval_neg_one_of_mod_four_eq_one (p := p) hp₂ hp₄, one_mul]

/-- If `p ≡ 3 (mod 4)`, the sign-detecting trace invariant is minus the
quadratic Gauss sum. -/
theorem quadraticDftTraceInvariant_eq_neg_gaussSum_of_mod_four_eq_three
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 3) :
    quadraticDftTraceInvariant p =
      -gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p)) := by
  rw [quadraticDftTraceInvariant_nonquadratic_contributions_cancel (p := p) hp₂,
    quadraticCharComplex_eval_neg_one_of_mod_four_eq_three (p := p) hp₂ hp₄, neg_one_mul]

end SignInvariant

end BernoulliRegular
