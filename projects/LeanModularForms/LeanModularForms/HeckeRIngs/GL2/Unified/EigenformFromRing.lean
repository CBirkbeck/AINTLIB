/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.Unified.NebentypusHeckeRingHom
import LeanModularForms.HeckeRIngs.GL2.Newforms

/-!
# Eigenforms come from the Hecke ring action

This file connects the cusp-form Hecke operators used in the definition of an `Eigenform`
to the canonical `Γ₀(N)` Hecke ring action `heckeRingHomCharSpace` of
`NebentypusHeckeRingHom.lean`.

The composite-`n` modular-form bridge `heckeRingHomCharSpace_heckeRingDn` identifies, for
`n` coprime to `N`, the concrete operator `heckeT_n` (restricted to `modFormCharSpace k χ`)
with `χ(n)⁻¹` times the ring image of the explicit element `heckeRingDn n ∈ 𝕋(Γ₀(N))`.
Since `heckeT_n_cusp` is the restriction of `heckeT_n` to cusp forms
(`heckeT_n_cusp_toModularForm'`), the same identity holds for the cusp operator on the
coercion of a `χ`-cusp form.  Consequently the Hecke operators in the `Eigenform`
definition are precisely the ring action, and an `Eigenform` is a simultaneous eigenvector
of the ring.

## Main results

* `Eigenform.isRingEigenvector` : the modular-form coercion of an `Eigenform` (whose
  coercion lies in `modFormCharSpace k χ`) is a simultaneous eigenvector of the ring action:
  `heckeRingHomCharSpace (heckeRingDn n) (↑f) = (χ(n)⁻¹ · eigenvalue n) • (↑f)`.
* `isRingEigenvector_of_isEigenform` : the predicate-level version — any `χ`-cusp form
  satisfying `IsEigenform` has modular-form coercion a simultaneous eigenvector of the ring
  action (with eigenvalues `χ(n)⁻¹ · aₙ`).

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005],
  §5.5 (eigenforms and the Hecke algebra).
* [G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*][shimura1971],
  §3.4–3.5.
-/

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup HeckeRing HeckeRing.GLn
open scoped ModularForm UpperHalfPlane

namespace HeckeRing.GL2.Unified

open HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

/-- **Eigenforms are ring eigenvectors.** If the modular-form coercion of an `Eigenform`
`f` lies in `modFormCharSpace k χ`, then `↑f` is a simultaneous eigenvector of the canonical
`Γ₀(N)` Hecke ring action: for each `n` coprime to `N`,
`heckeRingHomCharSpace (heckeRingDn n) (↑f) = (χ(n)⁻¹ · eigenvalue n) • (↑f)`.

The eigenvalue for the ring action is `χ(n)⁻¹ · a_n`, where `a_n` is the classical Hecke
eigenvalue; the diamond factor `χ(n)⁻¹` is the normalization between the abstract
double-coset operator and the textbook `T_n`. -/
theorem Eigenform.isRingEigenvector (f : Eigenform N k)
    (hf : f.toCuspForm ∈ cuspFormCharSpace k χ)
    (n : ℕ+) (hn : Nat.Coprime n.val N) :
    haveI : NeZero n.val := ⟨n.pos.ne'⟩
    heckeRingHomCharSpace (k := k) (χ := χ) (heckeRingDn n.val)
        ⟨f.toCuspForm.toModularForm', cuspFormCharSpace_toModularForm'_mem hf⟩ =
      ((↑(χ (ZMod.unitOfCoprime n.val hn)) : ℂ)⁻¹ * f.eigenvalue n) •
        (⟨f.toCuspForm.toModularForm', cuspFormCharSpace_toModularForm'_mem hf⟩ :
          modFormCharSpace k χ) := by
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  apply Subtype.ext
  rw [heckeRingHomCharSpace_heckeRingDn (k := k) (χ := χ) n.val hn]
  simp only [LinearMap.smul_apply, SetLike.val_smul, heckeT_n_charRestrict_coe]
  have heig : (heckeT_n_cusp k n.val f.toCuspForm).toModularForm' =
      f.eigenvalue n • f.toCuspForm.toModularForm' := by rw [f.isEigen n hn]; rfl
  rw [heckeT_n_cusp_toModularForm' n.val f.toCuspForm] at heig
  rw [heig, smul_smul]

/-- The predicate-level statement: a cusp form in `cuspFormCharSpace k χ` that is an
eigenform has modular-form coercion a simultaneous ring eigenvector. -/
theorem isRingEigenvector_of_isEigenform
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ)
    (hev : IsEigenform f) :
    ∃ a : ℕ+ → ℂ, ∀ n : ℕ+, Nat.Coprime n.val N →
      haveI : NeZero n.val := ⟨n.pos.ne'⟩
      heckeRingHomCharSpace (k := k) (χ := χ) (heckeRingDn n.val)
          ⟨f.toModularForm', cuspFormCharSpace_toModularForm'_mem hf⟩ =
        a n • (⟨f.toModularForm', cuspFormCharSpace_toModularForm'_mem hf⟩ :
          modFormCharSpace k χ) := by
  obtain ⟨a, ha⟩ := hev
  refine ⟨fun n ↦ if h : Nat.Coprime n.val N then
    (↑(χ (ZMod.unitOfCoprime n.val h)) : ℂ)⁻¹ * a n else 0, fun n hn ↦ ?_⟩
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  apply Subtype.ext
  rw [heckeRingHomCharSpace_heckeRingDn (k := k) (χ := χ) n.val hn]
  simp only [LinearMap.smul_apply, SetLike.val_smul, heckeT_n_charRestrict_coe, dif_pos hn]
  have heig : (heckeT_n_cusp k n.val f).toModularForm' =
      a n • f.toModularForm' := by rw [ha n hn]; rfl
  rw [heckeT_n_cusp_toModularForm' n.val f] at heig
  rw [heig, smul_smul]

end HeckeRing.GL2.Unified
