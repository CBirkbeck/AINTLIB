import BernoulliRegular.FLT37.Eichler.CaseII.LeadingExponent.KummerMatrixKernelCollapse
import BernoulliRegular.FLT37.Eichler.CaseII.LeadingExponent.GaloisEigenspaceCollapse

/-!
# Washington Exercise 8.11 for `p = 37`: the eigenbasis ↔ Dwork-log Vandermonde compatibility

This file discharges the **last** named residual of R3 (Washington Exercise 8.11) for `p = 37`,
`CaseIIEx811EigenVandermonde37` (`CaseIIEx811Core.lean`).  Together with the proven matrix-kernel
collapse of `CaseIIEx811Core.lean` (§1–§3 there) this closes `LeadingExponentEx811Core37`, hence
the leaf `LeadingExponentEigenCollapse37` (via the proven chain
`leadingExponentEigenCollapse37_of_eigenVandermonde`).

It imports only — it does **not** modify any existing file.

## The two-Vandermonde coincidence, made concrete

Two bases of the mod-`37` free part `(E_K free)/37` enter Exercise 8.11:

* the **generator basis** `g_a = φ(CPlusGenerator a) = [realCyclotomicUnit(a+2)]`
  (`a : Fin 17`, the half-range cyclotomic units `2, …, 18`), which is *linearly independent* by
  the proven `CPlusGenerator_image_linearIndependent` (under the proven all-nonzero certificate
  `caseIIGaloisEigen_pollaczekClasses_ne_zero`); and
* the **Galois eigenbasis** `E_{j'} = [pollaczekUnit(2(j'+1))]` (`j' : Fin 18`,
  `caseIIConjugateResidue_eigenvector`), the `Δ`-eigenvectors with eigenvalues `2^{2(j'+1)}`.

The change of basis is the *second* Vandermonde, read off the proven product expansion
`pollaczekUnitPlus(i) = ∏_b realCyclotomicUnit(b)^{b^{36-i}}`: in `(E_K free)/37`,

  `2 • E_{j'} = ∑_a (a+2)^{34-2j'} • g_a`                                              (★)

(`realUnitToFreePartModP_pollaczekUnitPlusKplus` gives the factor `2`; the product expansion is
`pollaczekUnitPlusKplus_eq_CPlusExponentProduct` + `realUnitToFreePartModP_CPlusExponentProduct`,
with `i = 2(j'+1)`, so `36 - i = 34 - 2j'`).

For `x = ∑_a e_a g_a` the canonical eigencoordinate `c_{j'} =`
`caseIIResidueProvenance_decomp x j'` (`c_{17} = 0`) is the unique solution of
`x = ∑_{j'} c_{j'} E_{j'}`.  Substituting (★) and using the **linear independence** of the `g_a`
inverts the relation to

  `(e_a : ZMod 37) = ∑_{j'} c_{j'} · 2⁻¹ (a+2)^{34-2j'}`.                              (♦)

Feeding (♦) into the Dwork-log Vandermonde row
`(V·ē)_j = ∑_a ((a+2)^{2(j+1)} - 1) ē_a` gives

  `(V·ē)_j = ∑_{j'} c_{j'} · M(j, j')`,   `M(j,j') = ∑_a ((a+2)^{2(j+1)}-1) · 2⁻¹ (a+2)^{34-2j'}`.

The finite-field matrix `M` is **diagonal** — `M(j,j') = 9·[j = j']` for `j, j' < 17` — by the
power-sum vanishing `∑_{n=2}^{18} n^{2m} ≡ -1 (mod 37)` for `2 ≤ 2m ≤ 34` versus
`∑_{n=2}^{18} n^{36} ≡ -3·2⁻¹`, verified directly by `decide` (`caseIIEx811Eigen_matrix_diagonal`).
The `j' = 17` column is irrelevant because `c_{17} = 0`
(`caseIIResidueProvenance_decomp_principal_zero`).
Hence `(V·ē)_j = 9 c_j` for every regular `j < 17`; the hypothesis `(V·ē)_j = 0` forces `c_j = 0`,
and `c_{17} = 0` is automatic.  This is the eigenbasis ↔ Dwork-log Vandermonde compatibility.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, Exercise 8.11 (p. 166),
  §8.3 (Theorem 8.16), §9.2 Lemma 9.9 (pp. 180–181).
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular (CPlusGenerator)
open BernoulliRegular.CyclotomicUnits

/-! ## 1. The change-of-basis relation (★)

The proven product expansion of the symmetrised Pollaczek unit, pushed to the mod-`37` free part,
expresses `2 • [pollaczekUnit i]` as a `(a+2)^{36-i}`-combination of the generator images. -/

/-- **(★): the eigenvector in terms of the generators** (proven, axiom-clean).  In the mod-`37`
free part `(E_K free)/37`,

  `2 • [pollaczekUnit i] = ∑_a ((a+2)^{36-i} : ℤ) • φ(CPlusGenerator a)`,

read off the proven product expansion `pollaczekUnitPlusKplus i = CPlusExponentProduct 0
(fun a ↦ (a+2)^{36-i})` (`pollaczekUnitPlusKplus_eq_CPlusExponentProduct`) together with
`realUnitToFreePartModP_pollaczekUnitPlusKplus` (the factor `2` from the σ-symmetrisation) and
the linearity `realUnitToFreePartModP_CPlusExponentProduct`. -/
theorem caseIIEx811Eigen_two_smul_pollaczek_eq
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (i : ℕ) :
    (2 : ℕ) • cyclotomicUnitToFreePartModPAdd (p := 37) (CyclotomicField 37 ℚ)
        (Additive.ofMul (FLT37.pollaczekUnit 37 (CyclotomicField 37 ℚ) i)) =
      ∑ a : Fin ((37 - 3) / 2),
        ((((a : ℕ) + 2) ^ (37 - 1 - i) : ℕ) : ℤ) •
          FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ)
            (Additive.ofMul
              (CPlusGenerator (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a)) := by
  rw [← FLT37.realUnitToFreePartModP_pollaczekUnitPlusKplus (K := CyclotomicField 37 ℚ) i,
    FLT37.pollaczekUnitPlusKplus_eq_CPlusExponentProduct i,
    FLT37.realUnitToFreePartModP_CPlusExponentProduct]

/-- The generator image `g_a = φ(CPlusGenerator a)`, abbreviated. -/
private abbrev genImg
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (a : Fin ((37 - 3) / 2)) : CyclotomicUnitFreePartModP (p := 37) (CyclotomicField 37 ℚ) :=
  FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ)
    (Additive.ofMul (CPlusGenerator (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a))

/-- **(★′): the eigenvector as an explicit `ZMod 37`-combination of the generators** (proven).

  `caseIIConjugateResidue_eigenvector j' = ∑_a (2⁻¹ · (a+2)^{34-2j'} : ZMod 37) • g_a`,

obtained from `caseIIEx811Eigen_two_smul_pollaczek_eq` (with `i = 2(j'+1)`, so `36 - i = 34 - 2j'`)
by multiplying through by `2⁻¹` and converting the `ℤ`-scalars to `ZMod 37`. -/
theorem caseIIEx811Eigen_eigenvector_eq_smul_genImg
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (j' : Fin 18) :
    caseIIConjugateResidue_eigenvector j' =
      ∑ a : Fin ((37 - 3) / 2),
        ((2 : ZMod 37)⁻¹ * (((a : ℕ) + 2 : ℕ) : ZMod 37) ^ (34 - 2 * (j' : ℕ))) • genImg a := by
  have h2 : (2 : ZMod 37) ≠ 0 := by decide
  -- (★) at i = 2(j'+1).
  have hstar := caseIIEx811Eigen_two_smul_pollaczek_eq (2 * ((j' : ℕ) + 1))
  -- 37 - 1 - 2(j'+1) = 34 - 2j'.
  have hexp : (37 : ℕ) - 1 - 2 * ((j' : ℕ) + 1) = 34 - 2 * (j' : ℕ) := by
    have : (j' : ℕ) < 18 := j'.isLt
    omega
  rw [hexp] at hstar
  -- The LHS of hstar is `2 • eigvec j'` definitionally (eigenvector = [pollaczekUnit 2(j'+1)]).
  -- so hstar : 2 • eigvec j' = ∑_a ((a+2)^{34-2j'} : ℤ) • g_a.
  have hstar' : (2 : ZMod 37) • caseIIConjugateResidue_eigenvector j' =
      ∑ a : Fin ((37 - 3) / 2),
        ((((a : ℕ) + 2 : ℕ) : ZMod 37) ^ (34 - 2 * (j' : ℕ))) • genImg a := by
    rw [show (2 : ZMod 37) • caseIIConjugateResidue_eigenvector j' =
          (2 : ℕ) • caseIIConjugateResidue_eigenvector j' by
        rw [← Nat.cast_smul_eq_nsmul (ZMod 37)]; norm_num]
    rw [show ((2 : ℕ) • caseIIConjugateResidue_eigenvector j' :
          CyclotomicUnitFreePartModP (p := 37) (CyclotomicField 37 ℚ)) =
        (2 : ℕ) • cyclotomicUnitToFreePartModPAdd (p := 37) (CyclotomicField 37 ℚ)
          (Additive.ofMul (FLT37.pollaczekUnit 37 (CyclotomicField 37 ℚ)
            (2 * ((j' : ℕ) + 1)))) from rfl]
    rw [hstar]
    refine Finset.sum_congr rfl (fun a _ ↦ ?_)
    rw [← Int.cast_smul_eq_zsmul (ZMod 37)]
    congr 1
    push_cast
    rfl
  -- Multiply by 2⁻¹ to invert: eigvec = 2⁻¹ • (2 • eigvec) = 2⁻¹ • RHS = ∑ (2⁻¹ * ...) • g.
  calc caseIIConjugateResidue_eigenvector j'
      = (2 : ZMod 37)⁻¹ • ((2 : ZMod 37) • caseIIConjugateResidue_eigenvector j') := by
        rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
    _ = (2 : ZMod 37)⁻¹ • ∑ a : Fin ((37 - 3) / 2),
          ((((a : ℕ) + 2 : ℕ) : ZMod 37) ^ (34 - 2 * (j' : ℕ))) • genImg a := by rw [hstar']
    _ = ∑ a : Fin ((37 - 3) / 2),
          ((2 : ZMod 37)⁻¹ * (((a : ℕ) + 2 : ℕ) : ZMod 37) ^ (34 - 2 * (j' : ℕ))) • genImg a := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl (fun a _ ↦ by rw [smul_smul])

/-! ## 2. The linear independence of the generator images and the inversion (♦)

The generator images `g_a` are linearly independent (the proven
`CPlusGenerator_image_linearIndependent`
under the proven all-nonzero certificate `caseIIGaloisEigen_pollaczekClasses_ne_zero`).  Combined
with (★′) and the canonical eigendecomposition `x = ∑_{j'} c_{j'} E_{j'}` this inverts the
change of basis: the `ZMod 37`-reduced exponent of `x = ∑_a e_a g_a` is the eigenbasis-combination
`(e_a : ZMod 37) = ∑_{j'} c_{j'} · 2⁻¹ (a+2)^{34-2j'}`. -/

/-- **The generator images are linearly independent** (proven re-export). -/
theorem caseIIEx811Eigen_genImg_linearIndependent
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    LinearIndependent (ZMod 37) (fun a : Fin ((37 - 3) / 2) ↦ genImg a) :=
  FLT37.CPlusGenerator_image_linearIndependent (K := CyclotomicField 37 ℚ)
    caseIIGaloisEigen_pollaczekClasses_ne_zero

/-- **(♦): the inversion of the change of basis** (proven, axiom-clean).  For an integer exponent
vector `e : Fin 17 → ℤ` and `c = caseIIResidueProvenance_decomp (∑_a e_a g_a)` (the canonical
eigencoordinates), the `ZMod 37`-reduced exponent equals the eigenbasis combination

  `(e_a : ZMod 37) = ∑_{j'} c_{j'} · 2⁻¹ (a+2)^{34-2j'}`,

for every `a`.  Proof: both `∑_a (e_a:ZMod37) • g_a` and
`∑_a (∑_{j'} c_{j'} 2⁻¹(a+2)^{34-2j'}) • g_a`
equal `x` (the first by definition; the second by the decomposition spec
`caseIIResidueProvenance_decomp_spec` and the eigenvector expansion (★′)), so the coefficients
match by the linear independence of the `g_a`. -/
theorem caseIIEx811Eigen_exponent_eq
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (e : Fin ((37 - 3) / 2) → ℤ) (a : Fin ((37 - 3) / 2)) :
    ((e a : ℤ) : ZMod 37) =
      ∑ j' : Fin 18,
        caseIIResidueProvenance_decomp (∑ b : Fin ((37 - 3) / 2), e b • genImg b) j' *
          ((2 : ZMod 37)⁻¹ * (((a : ℕ) + 2 : ℕ) : ZMod 37) ^ (34 - 2 * (j' : ℕ))) := by
  set x : CyclotomicUnitFreePartModP (p := 37) (CyclotomicField 37 ℚ) :=
    ∑ b : Fin ((37 - 3) / 2), e b • genImg b with hx
  set c := caseIIResidueProvenance_decomp x with hc
  -- x = ∑_a (e_a : ZMod 37) • g_a.
  have hx1 : x = ∑ b : Fin ((37 - 3) / 2), ((e b : ℤ) : ZMod 37) • genImg b := by
    rw [hx]
    exact Finset.sum_congr rfl (fun b _ ↦ (Int.cast_smul_eq_zsmul (ZMod 37) (e b) _).symm)
  -- x = ∑_a (∑_{j'} c_{j'} 2⁻¹(a+2)^{34-2j'}) • g_a, via the decomp spec + (★′).
  have hx2 : x = ∑ b : Fin ((37 - 3) / 2),
      (∑ j' : Fin 18, c j' * ((2 : ZMod 37)⁻¹ *
        (((b : ℕ) + 2 : ℕ) : ZMod 37) ^ (34 - 2 * (j' : ℕ)))) • genImg b := by
    -- ∑_{j'} c_{j'} • eigvec_{j'} = ∑_{j'} c_{j'} • ∑_a (2⁻¹(a+2)^{34-2j'}) • g_a
    --   = ∑_a (∑_{j'} c_{j'} 2⁻¹(a+2)^{34-2j'}) • g_a.
    have hspec : x = ∑ j' : Fin 18, c j' • caseIIConjugateResidue_eigenvector j' := by
      rw [hc]; exact caseIIResidueProvenance_decomp_spec x
    have hstep : x = ∑ j' : Fin 18, c j' •
        ∑ b : Fin ((37 - 3) / 2),
          ((2 : ZMod 37)⁻¹ * (((b : ℕ) + 2 : ℕ) : ZMod 37) ^ (34 - 2 * (j' : ℕ))) • genImg b := by
      rw [hspec]
      refine Finset.sum_congr rfl (fun j' _ ↦ ?_)
      simp only [caseIIEx811Eigen_eigenvector_eq_smul_genImg]
    rw [hstep]
    -- Distribute c j' • into the inner sum, then swap the order of summation.
    rw [show (∑ j' : Fin 18, c j' •
          ∑ b : Fin ((37 - 3) / 2),
            ((2 : ZMod 37)⁻¹ * (((b : ℕ) + 2 : ℕ) : ZMod 37) ^ (34 - 2 * (j' : ℕ))) • genImg b) =
        ∑ j' : Fin 18, ∑ b : Fin ((37 - 3) / 2),
          (c j' * ((2 : ZMod 37)⁻¹ * (((b : ℕ) + 2 : ℕ) : ZMod 37) ^ (34 - 2 * (j' : ℕ)))) •
            genImg b
        from Finset.sum_congr rfl (fun j' _ ↦ by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl (fun b _ ↦ by rw [smul_smul]))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ ↦ ?_)
    rw [Finset.sum_smul]
  -- Match coefficients by linear independence: ∑ (f_b - h_b) • g_b = 0 ⟹ f_b = h_b.
  have hli := caseIIEx811Eigen_genImg_linearIndependent
  set f : Fin ((37 - 3) / 2) → ZMod 37 := fun b ↦ ((e b : ℤ) : ZMod 37) with hf
  set h : Fin ((37 - 3) / 2) → ZMod 37 := fun b ↦
    ∑ j' : Fin 18, c j' * ((2 : ZMod 37)⁻¹ *
      (((b : ℕ) + 2 : ℕ) : ZMod 37) ^ (34 - 2 * (j' : ℕ))) with hh
  have heq0 : ∑ b : Fin ((37 - 3) / 2), (f b - h b) • genImg b = 0 := by
    rw [show (∑ b : Fin ((37 - 3) / 2), (f b - h b) • genImg b) =
        (∑ b : Fin ((37 - 3) / 2), f b • genImg b) -
          ∑ b : Fin ((37 - 3) / 2), h b • genImg b by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun b _ ↦ sub_smul (f b) (h b) (genImg b))]
    rw [← hx1, ← hx2, sub_self]
  have hzero := Fintype.linearIndependent_iff.mp hli (fun b ↦ f b - h b) heq0 a
  have hfa : f a = h a := sub_eq_zero.mp hzero
  rw [hf, hh] at hfa
  exact hfa

/-! ## 3. The two-Vandermonde matrix is diagonal, and the collapse

Feeding (♦) into the Dwork-log Vandermonde row gives `(V·ē)_j = ∑_{j'} c_{j'} · M(j,j')` where
`M(j,j') = ∑_a (((a+2)²)^{j+1} - 1) · 2⁻¹ (a+2)^{34-2j'}`.  The finite-field matrix `M` is diagonal,
`M(j,j') = 9·[j = j']` for `j, j' < 17`, by the power-sum identity over `{2,…,18}` (`decide`). -/

/-- **The two-Vandermonde matrix is diagonal — the inverse-free `2`-scaled form** (proven by
`decide`).  This is `caseIIEx811Eigen_matrix_diagonal` with the constant factor `2⁻¹` pulled out of
every term, so the RHS is doubled (`18 = 2 · 9` in `𝔽₃₇`):

  `∑_a (((a+2)²)^{m+1} - 1) · (a+2)^{34-2m'} = (if m = m' then 18 else 0)`   in `𝔽₃₇`.

It contains **no field inverse** (only `+`, `*`, `^`, `-`, `=` over `ZMod 37`), so it is
kernel-reducible by `decide` under Lean 4.31 / mathlib `1680840` (where `ZMod` field inverse is
defined by well-founded `Nat.gcdA` recursion and no longer reduces in the kernel).  It is the
power-sum core `∑_{n=2}^{18} n^{2m} ≡ -1` (`2 ≤ 2m ≤ 34`) and `∑_{n=2}^{18} n^{36} ≡ -3` of
Washington's two-Vandermonde coincidence.  No `Fact (Nat.Prime 37)` is in scope (it blocks
`decide`). -/
private theorem caseIIEx811Eigen_matrix_diagonal_two_smul :
    ∀ m m' : Fin 17,
      (∑ a : Fin ((37 - 3) / 2),
        (((((a : ℕ) + 2 : ℕ) : ZMod 37) ^ 2) ^ ((m : ℕ) + 1) - 1) *
          ((((a : ℕ) + 2 : ℕ) : ZMod 37) ^ (34 - 2 * (m' : ℕ)))) =
        (if (m : ℕ) = (m' : ℕ) then 18 else 0) := by
  decide

/-- **The two-Vandermonde matrix is diagonal** (proven, axiom-clean).  For `j, j' : Fin 18` with
`j, j' < 17`,

  `∑_a (((a+2)² )^{j+1} - 1) · 2⁻¹ (a+2)^{34-2j'} = (if j = j' then 9 else 0)`   in `𝔽₃₇`.

This is the concrete form of Washington's two-Vandermonde coincidence: the Dwork-log Vandermonde
`((a+2)^{2(j+1)}-1)` paired against the Galois eigenbasis change-of-basis `2⁻¹(a+2)^{34-2j'}`
collapses to a nonzero diagonal (value `9`).  The mod-`37` power-sum identities
`∑_{n=2}^{18} n^{2m} ≡ -1` (`2 ≤ 2m ≤ 34`) and `∑_{n=2}^{18} n^{36} ≡ -3·2⁻¹` are the inverse-free
`caseIIEx811Eigen_matrix_diagonal_two_smul` (RHS doubled to `18`); here the constant `2⁻¹` is pulled
out of the sum (`Finset.mul_sum`) and `2⁻¹ · 18 = 9` / `2⁻¹ · 0 = 0` close the diagonal/off-diagonal
cases.  (`decide` no longer reduces the field inverse `2⁻¹` in the kernel under Lean 4.31.) -/
theorem caseIIEx811Eigen_matrix_diagonal :
    ∀ m m' : Fin 17,
      (∑ a : Fin ((37 - 3) / 2),
        (((((a : ℕ) + 2 : ℕ) : ZMod 37) ^ 2) ^ ((m : ℕ) + 1) - 1) *
          ((2 : ZMod 37)⁻¹ * (((a : ℕ) + 2 : ℕ) : ZMod 37) ^ (34 - 2 * (m' : ℕ)))) =
        (if (m : ℕ) = (m' : ℕ) then 9 else 0) := by
  intro m m'
  -- Pull the constant `2⁻¹` out of every term and reduce to the inverse-free doubled sum.
  have hfactor : (∑ a : Fin ((37 - 3) / 2),
        (((((a : ℕ) + 2 : ℕ) : ZMod 37) ^ 2) ^ ((m : ℕ) + 1) - 1) *
          ((2 : ZMod 37)⁻¹ * (((a : ℕ) + 2 : ℕ) : ZMod 37) ^ (34 - 2 * (m' : ℕ)))) =
      (2 : ZMod 37)⁻¹ *
        ∑ a : Fin ((37 - 3) / 2),
          (((((a : ℕ) + 2 : ℕ) : ZMod 37) ^ 2) ^ ((m : ℕ) + 1) - 1) *
            ((((a : ℕ) + 2 : ℕ) : ZMod 37) ^ (34 - 2 * (m' : ℕ))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a _ ↦ by ring)
  rw [hfactor, caseIIEx811Eigen_matrix_diagonal_two_smul m m']
  -- `2⁻¹ · 18 = 9` and `2⁻¹ · 0 = 0` in `𝔽₃₇`; pulling `18 = 2 · 9` clears the inverse.
  have h2 : (2 : ZMod 37) ≠ 0 := by decide
  by_cases h : (m : ℕ) = (m' : ℕ)
  · rw [if_pos h, if_pos h]
    rw [show (18 : ZMod 37) = 2 * 9 by decide, ← mul_assoc, inv_mul_cancel₀ h2, one_mul]
  · rw [if_neg h, if_neg h, mul_zero]

/-- **The two-Vandermonde collapse** (proven, axiom-clean): the canonical eigencoordinate of
`∑_a e_a g_a` at a regular index `j < 17` is `9⁻¹·(V·ē)_j`.  Concretely

  `(V·ē)_j = 9 · caseIIResidueProvenance_decomp (∑_a e_a g_a) j`   for `(j : ℕ) < 17`.

Proof: unfold `(V·ē)_j = ∑_a (((a+2)²)^{j+1}-1) (e_a : ZMod 37)`, substitute (♦)
(`caseIIEx811Eigen_exponent_eq`) for `(e_a : ZMod 37)`, swap the sums to get
`∑_{j'} c_{j'} M(j,j')`,
and apply the diagonal identity (`caseIIEx811Eigen_matrix_diagonal`) — the `j' < 17` terms collapse
to `9 c_j` and the single `j' = 17` term vanishes because `c_{17} = 0`
(`caseIIResidueProvenance_decomp_principal_zero`). -/
theorem caseIIEx811Eigen_vandermonde_eq_nine_smul
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (e : Fin ((37 - 3) / 2) → ℤ) (j : Fin (kummerLogRank 37)) :
    (vandermondeTeichmullerEvenSubOneMatrix (p := 37) (by norm_num)).mulVec
        (fun a : Fin ((37 - 3) / 2) ↦ (e a : ZMod 37)) j =
      (9 : ZMod 37) *
        caseIIResidueProvenance_decomp
          (∑ b : Fin ((37 - 3) / 2), e b • genImg b)
          ⟨(j : ℕ), by have := j.isLt; simp only [kummerLogRank] at this; omega⟩ := by
  set c := caseIIResidueProvenance_decomp (∑ b : Fin ((37 - 3) / 2), e b • genImg b) with hc
  -- Step 1: unfold the Vandermonde row to an explicit sum.
  rw [show (vandermondeTeichmullerEvenSubOneMatrix (p := 37) (by norm_num)).mulVec
        (fun a : Fin ((37 - 3) / 2) ↦ (e a : ZMod 37)) j =
      ∑ a : Fin ((37 - 3) / 2),
        (((((a : ℕ) + 2 : ℕ) : ZMod 37) ^ 2) ^ ((j : ℕ) + 1) - 1) * ((e a : ℤ) : ZMod 37)
      by
        rw [Matrix.mulVec]
        simp only [dotProduct, vandermondeTeichmullerEvenSubOneMatrix, teichmullerEvenNode,
          kummerLogColumnIndex, BernoulliRegular.CPlusGeneratorIndex]]
  -- Step 2: substitute (♦) for (e a : ZMod 37).
  rw [show (∑ a : Fin ((37 - 3) / 2),
        (((((a : ℕ) + 2 : ℕ) : ZMod 37) ^ 2) ^ ((j : ℕ) + 1) - 1) * ((e a : ℤ) : ZMod 37)) =
      ∑ a : Fin ((37 - 3) / 2),
        (((((a : ℕ) + 2 : ℕ) : ZMod 37) ^ 2) ^ ((j : ℕ) + 1) - 1) *
          ∑ j' : Fin 18, c j' *
            ((2 : ZMod 37)⁻¹ * (((a : ℕ) + 2 : ℕ) : ZMod 37) ^ (34 - 2 * (j' : ℕ)))
      from Finset.sum_congr rfl (fun a _ ↦ by rw [caseIIEx811Eigen_exponent_eq e a, ← hc])]
  -- Step 3: distribute and swap sums to ∑_{j'} c_{j'} M(j,j').
  rw [show (∑ a : Fin ((37 - 3) / 2),
        (((((a : ℕ) + 2 : ℕ) : ZMod 37) ^ 2) ^ ((j : ℕ) + 1) - 1) *
          ∑ j' : Fin 18, c j' *
            ((2 : ZMod 37)⁻¹ * (((a : ℕ) + 2 : ℕ) : ZMod 37) ^ (34 - 2 * (j' : ℕ)))) =
      ∑ j' : Fin 18, c j' *
        (∑ a : Fin ((37 - 3) / 2),
          (((((a : ℕ) + 2 : ℕ) : ZMod 37) ^ 2) ^ ((j : ℕ) + 1) - 1) *
            ((2 : ZMod 37)⁻¹ * (((a : ℕ) + 2 : ℕ) : ZMod 37) ^ (34 - 2 * (j' : ℕ))))
      by
        rw [show (∑ a : Fin ((37 - 3) / 2),
              (((((a : ℕ) + 2 : ℕ) : ZMod 37) ^ 2) ^ ((j : ℕ) + 1) - 1) *
                ∑ j' : Fin 18, c j' *
                  ((2 : ZMod 37)⁻¹ * (((a : ℕ) + 2 : ℕ) : ZMod 37) ^ (34 - 2 * (j' : ℕ)))) =
            ∑ a : Fin ((37 - 3) / 2), ∑ j' : Fin 18,
              c j' * ((((((a : ℕ) + 2 : ℕ) : ZMod 37) ^ 2) ^ ((j : ℕ) + 1) - 1) *
                ((2 : ZMod 37)⁻¹ * (((a : ℕ) + 2 : ℕ) : ZMod 37) ^ (34 - 2 * (j' : ℕ))))
            from Finset.sum_congr rfl (fun a _ ↦ by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl (fun j' _ ↦ by ring))]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j' _ ↦ ?_)
        rw [Finset.mul_sum]]
  -- Step 4: split off the j' = 17 term (killed by c 17 = 0) and apply the diagonal identity.
  have hj17 : (j : ℕ) < 17 := j.isLt
  rw [Fin.sum_univ_castSucc]
  -- the last term j' = Fin.last 17 has c (Fin.last 17) = c 17 = 0.
  rw [show c (Fin.last 17) = 0 by
    rw [hc]
    have : (Fin.last 17 : Fin 18) = (17 : Fin 18) := by decide
    rw [this]; exact caseIIResidueProvenance_decomp_principal_zero _]
  rw [zero_mul, add_zero]
  -- The remaining sum over Fin.castSucc k (k : Fin 17), apply the diagonal.
  rw [show (∑ k : Fin 17, c (Fin.castSucc k) *
        (∑ a : Fin ((37 - 3) / 2),
          (((((a : ℕ) + 2 : ℕ) : ZMod 37) ^ 2) ^ ((j : ℕ) + 1) - 1) *
            ((2 : ZMod 37)⁻¹ *
              (((a : ℕ) + 2 : ℕ) : ZMod 37) ^ (34 - 2 * ((Fin.castSucc k : Fin 18) : ℕ))))) =
      ∑ k : Fin 17, c (Fin.castSucc k) *
        (if ((⟨(j : ℕ), hj17⟩ : Fin 17) : ℕ) = (k : ℕ) then (9 : ZMod 37) else 0)
      from Finset.sum_congr rfl (fun k _ ↦ by
        rw [show ((Fin.castSucc k : Fin 18) : ℕ) = (k : ℕ) from Fin.val_castSucc k]
        rw [caseIIEx811Eigen_matrix_diagonal ⟨(j : ℕ), hj17⟩ k])]
  -- Only the k with (k:ℕ) = (j:ℕ) survives; that is k = ⟨j, _⟩, contributing 9 c_j.
  rw [Finset.sum_eq_single (⟨(j : ℕ), hj17⟩ : Fin 17)]
  · rw [if_pos rfl]
    rw [show (Fin.castSucc (⟨(j : ℕ), hj17⟩ : Fin 17) : Fin 18) =
        (⟨(j : ℕ), by omega⟩ : Fin 18) by
      apply Fin.ext; rw [Fin.val_castSucc]]
    ring
  · intro k _ hk
    rw [if_neg (by
      intro heq
      exact hk (Fin.ext heq.symm))]
    rw [mul_zero]
  · intro hcontra
    exact absurd (Finset.mem_univ _) hcontra

/-! ## 4. The main theorem: `CaseIIEx811EigenVandermonde37`

For every `C⁺` exponent vector `e` whose Dwork-log Vandermonde rows vanish at the regular rows
`j : Fin (kummerLogRank 37)` (`j ≠ 15`), the canonical mod-`37` free-part eigencoordinate of
`∑_a e_a g_a` vanishes at every regular index `j : Fin 18`, `j ≠ 15`.  The `j = 17`
(principal-character) coordinate is `0` automatically
(`caseIIResidueProvenance_decomp_principal_zero`);
each regular `j < 17` matches a regular Vandermonde row `j_17`, and the collapse
`caseIIEx811Eigen_vandermonde_eq_nine_smul` gives `9 · c_j = (V·ē)_{j_17} = 0`, whence `c_j = 0`. -/

/-- **`CaseIIEx811EigenVandermonde37`, proven** (axiom-clean).  This discharges the last named
residual of R3 (Washington Exercise 8.11) for `p = 37`: the Galois-eigenbasis vs Dwork-log
Vandermonde change-of-basis compatibility.

Via the proven chain `leadingExponentEigenCollapse37_of_eigenVandermonde` (which composes the
matrix-kernel collapse of `CaseIIEx811Core.lean` §1–§3 with this residual), proving it **closes**
`LeadingExponentEx811Core37`, hence the leaf `LeadingExponentEigenCollapse37`.

The proof is the concrete two-Vandermonde coincidence: the change of basis (★)
`2 • [pollaczekUnit(2(j'+1))] = ∑_a (a+2)^{34-2j'} • g_a`, inverted against the *linearly
independent* generator images (♦), turns the Dwork-log Vandermonde row into the diagonal
finite-field matrix `caseIIEx811Eigen_matrix_diagonal` (value `9`); the regular rows then read off
the regular eigencoordinates. -/
theorem caseIIEx811EigenVandermonde37_proven
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    CaseIIEx811EigenVandermonde37 := by
  intro e hvan j hj
  -- The free-part class `x`.
  by_cases hj17 : (j : ℕ) = 17
  · -- The principal-character coordinate `c 17` is automatically `0`.
    have : j = (17 : Fin 18) := Fin.ext (by rw [hj17]; rfl)
    rw [this]
    exact caseIIResidueProvenance_decomp_principal_zero _
  · -- `j < 17`: a regular Vandermonde row.
    have hjlt : (j : ℕ) < 17 := by have := j.isLt; omega
    -- The matching Vandermonde-row index `j_17 : Fin (kummerLogRank 37)`, with `j17.1 = j.1`.
    set j17 : Fin (kummerLogRank 37) := ⟨(j : ℕ), by simp only [kummerLogRank]; omega⟩ with hj17def
    have hj17val : (j17 : ℕ) = (j : ℕ) := rfl
    have hj17ne : (j17 : ℕ) ≠ 15 := by
      rw [hj17val]
      intro hcontra
      exact hj (Fin.ext (by rw [hcontra]; rfl))
    -- The collapse: `(V·ē)_{j17} = 9 · decomp x ⟨j17.1, _⟩`.
    have hcollapse := caseIIEx811Eigen_vandermonde_eq_nine_smul e j17
    -- The hypothesis kills the regular row.
    have hzero := hvan j17 hj17ne
    rw [hcollapse] at hzero
    -- `9 ≠ 0` mod 37 ⟹ the eigencoordinate is `0`.
    have h9 : (9 : ZMod 37) ≠ 0 := by decide
    -- Extract `decomp x ⟨j17.1, _⟩ = 0` from `9 * (·) = 0`, then transport the index to `j`.
    have hcj := (mul_eq_zero.mp hzero).resolve_left h9
    -- The goal `decomp x j = 0` matches `hcj` (`⟨j17.1, _⟩ = j`, same Nat value; defeq).
    rw [← hcj]

end BernoulliRegular.FLT37.Eichler

end
