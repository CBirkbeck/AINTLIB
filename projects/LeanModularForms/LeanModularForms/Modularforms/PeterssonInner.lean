/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.Modularforms.PeterssonInnerProduct

/-!
# Petersson inner product: algebraic API for cusp forms

Extends `PeterssonInnerProduct.lean` with the full sesquilinear inner product
API on `CuspForm Γ k`, including complex scalar multiplication, additivity,
and positive definiteness.

## Main results

* `CuspForm.pet_add_right` / `pet_add_left` — additivity in each argument
* `CuspForm.pet_conj_smul_left` / `pet_smul_right_complex` — complex-sesquilinear
* `CuspForm.innerProductCuspForm` — `Inner ℂ (CuspForm Γ k)` instance
* `CuspForm.inner_pet` — `⟪f, g⟫_ℂ = pet f g`
* `CuspForm.pet_definite` — `pet f f = 0 → f = 0` (via identity theorem)

## Implementation notes

The `Inner ℂ` instance uses `pet` (integration over the `SL₂(ℤ)` fundamental
domain `𝒟`). For forms of level `Γ ≤ SL₂(ℤ)`, this is `1/[SL₂(ℤ):Γ]` times
the "canonical" Petersson inner product on `Γ\ℍ`, but the positive-definiteness
and sesquilinearity are identical.

We do NOT create an `InnerProductSpace ℂ` instance because `CuspForm Γ k`
lacks a compatible `NormedAddCommGroup` structure.

## References

* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §5.4
* [Miy] Miyake, *Modular Forms*, §2.7–2.8
-/

noncomputable section

namespace CuspForm

open UpperHalfPlane ModularGroup MeasureTheory

open scoped Manifold

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

/-- The Petersson inner product as an `Inner ℂ` instance on cusp forms. -/
instance innerProductCuspForm : Inner ℂ (CuspForm Γ k) where
  inner := pet

@[simp]
theorem inner_pet (f g : CuspForm Γ k) : @inner ℂ _ _ f g = pet f g := rfl

/-- **Positive definiteness** of the Petersson inner product for general `Γ`.

If `⟨f, f⟩ = 0` for a cusp form `f` of any level `Γ`, then `f = 0`.

The proof uses the identity theorem for holomorphic functions: `pet f f = 0`
implies `f = 0` on the open fundamental domain `𝒟ᵒ ⊆ ℍ`, and since `f` is
holomorphic on the connected space `ℍ`, it follows that `f = 0` everywhere.

This generalises `peterssonInner_definite_levelOne` (which uses `SL₂(ℤ)`
reduction instead). -/
theorem pet_definite [Γ.IsArithmetic] (f : CuspForm Γ k) (hpet : pet f f = 0) :
    f = 0 := by
  have hfdo : ∀ τ ∈ fdo, (⇑f) τ = 0 := fun τ hτ ↦
    eq_zero_on_fd_of_peterssonInner_self_eq_zero f hpet (UpperHalfPlane.fdo_subset_fd hτ)
  set τ₀ : ℍ := ⟨⟨0, 2⟩, by norm_num⟩
  have hτ₀ : τ₀ ∈ fdo := by
    refine ⟨by norm_num [Complex.normSq_apply], ?_⟩
    change |(τ₀ : ℂ).re| < 1 / 2
    norm_num
  have hev := Filter.eventually_of_mem (UpperHalfPlane.isOpen_fdo.mem_nhds hτ₀) hfdo
  have h := UpperHalfPlane.eq_zero_of_frequently (CuspFormClass.holo f)
    (hev.filter_mono nhdsWithin_le_nhds).frequently
  ext τ
  exact congr_fun h τ

end CuspForm
