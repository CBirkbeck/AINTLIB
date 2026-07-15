/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Ticket T-DEV1b (finite free resolutions).
-/
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finite free resolutions over a Noetherian ring (Stacks Tag 00LP)

Over a **Noetherian** commutative ring `S`, every finitely generated `S`-module `M` admits a
resolution by *finite free* modules, and each syzygy (kernel of a differential) is again a finite
module.  This is Stacks Tag **00LP**.  The mathematical content is entirely the Noetherian
bookkeeping: a submodule of a finite free module over a Noetherian ring is again finite, so the
kernels never leave the world of finite modules and the construction iterates.

## Main results

* `Module.exists_finite_free_surjective_finite_ker` — the **first syzygy is finite**: a finite
  module over a Noetherian ring is covered by a finite free module `Sᵏ ↠ M` whose kernel is again
  finite.  This is the atom the whole file is built from and the form consumed downstream.

The remaining declarations assemble these atoms into an honest, explicit resolution
`⋯ → F₂ → F₁ → F₀ → M → 0` by finite free modules `Fₙ = S^{freeRank n}` (`Fin (freeRank n) → S`):

* `FiniteFreeResolution.aug` / `aug_surjective` — the augmentation `ε : F₀ ↠ M`.
* `FiniteFreeResolution.d` — the differentials `dₙ : F_{n+1} →ₗ Fₙ`.
* `FiniteFreeResolution.range_d_zero`, `range_d_succ` — **exactness**:
  `range d₀ = ker ε` and `range d_{n+1} = ker dₙ`.
* `FiniteFreeResolution.d_comp_d`, `aug_comp_d_zero` — the complex identities `dₙ ∘ d_{n+1} = 0`.
* `FiniteFreeResolution.finite_ker_aug`, `finite_ker_d` — **every syzygy is finite**
  (`Kₙ = ker(F_{n-1} → F_{n-2})`).

The `n`-th syzygy in the sense of Stacks 00LP is `ker ε` (for `n = 1`) and `ker dₙ` (for
`n ≥ 2`); by exactness these equal the images `range d₀`, `range d_{n+1}`.  Each resolution term
`Fin (freeRank n) → S` is automatically finite (`Module.Finite`) and free (`Module.Free`).

## Design notes

Everything lives in `S`'s universe with **canonical** module instances: each syzygy is a genuine
`Submodule S (Fin k → S)` (never an opaque bundled carrier), so `Module.Finite` is found by
instance resolution through `isNoetherian_pi'` → `isNoetherian_submodule'` → `IsNoetherian.finite`,
and exactness reduces to `LinearMap` range/kernel algebra with no coercion friction.

A `CategoryTheory.ProjectiveResolution` / `HomologicalComplex` packaging (to plug into mathlib's
`HasProjectiveDimensionLE` / `Ext` API) can be layered on top of `aug`/`d`/`range_d_succ` but is
not needed by the immediate consumer (flat-locus openness, Stacks 00RC), which uses the concrete
syzygy finiteness above.

## References

* [Stacks Tag 00LP](https://stacks.math.columbia.edu/tag/00LP)
-/

open Function

universe u v

namespace Module

/-- **First syzygy is finite** (Stacks 00LP, base case).  A finitely generated module `M` over a
Noetherian commutative ring `S` is covered by a finite free module `Sᵏ ↠ M` whose kernel is again
a finite `S`-module.

The surjection is `Module.Finite.exists_fin'` (a finite generating set); finiteness of the kernel
is pure Noetherian bookkeeping — `Fin k → S` is a Noetherian module (`isNoetherian_pi'`), hence so
is its submodule `ker f` (`isNoetherian_submodule'`), hence `ker f` is finite
(`IsNoetherian.finite`) — and is discharged here by instance resolution. -/
theorem exists_finite_free_surjective_finite_ker
    {S M : Type*} [CommRing S] [IsNoetherianRing S]
    [AddCommGroup M] [Module S M] [Module.Finite S M] :
    ∃ (k : ℕ) (f : (Fin k → S) →ₗ[S] M),
      Surjective f ∧ Module.Finite S (LinearMap.ker f) := by
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' S M
  exact ⟨k, f, hf, inferInstance⟩

end Module

namespace FiniteFreeResolution

variable (S : Type u) [CommRing S]

/-- A finite free cover of a **finite submodule** `K` of a finite free module `Fin b → S`, given as
a map *between free modules* `g : Fin a → S →ₗ Fin b → S` with `range g = K` (namely
`K.subtype ∘ₗ (a finite free cover of K)`).  Keeping `K` as a genuine submodule with its canonical
instances is what makes the exactness computations below coercion-free. -/
noncomputable def coverSub {b : ℕ} (K : Submodule S (Fin b → S)) [Module.Finite S K] :
    Σ a : ℕ, { g : (Fin a → S) →ₗ[S] (Fin b → S) // LinearMap.range g = K } :=
  let e := Module.Finite.exists_fin' S K
  ⟨e.choose, K.subtype ∘ₗ e.choose_spec.choose, by
    rw [LinearMap.range_comp, LinearMap.range_eq_top.2 e.choose_spec.choose_spec,
      Submodule.map_top, Submodule.range_subtype]⟩

variable (M : Type v) [AddCommGroup M] [Module S M] [Module.Finite S M]

/-- Augmentation data: a chosen finite free cover `ε : F₀ ↠ M`, packaged with the rank of `F₀`. -/
noncomputable def augData : Σ k : ℕ, { ε : (Fin k → S) →ₗ[S] M // Surjective ε } :=
  ⟨_, (Module.Finite.exists_fin' S M).choose_spec.choose,
    (Module.Finite.exists_fin' S M).choose_spec.choose_spec⟩

/-- Rank of the free module `F₀ = S^{augRank}` covering `M`. -/
noncomputable def augRank : ℕ := (augData S M).1

/-- The augmentation map `ε : F₀ →ₗ M` of the resolution. -/
noncomputable def aug : (Fin (augRank S M) → S) →ₗ[S] M := (augData S M).2.1

/-- The augmentation `ε : F₀ ↠ M` of the resolution is surjective. -/
theorem aug_surjective : Surjective (aug S M) := (augData S M).2.2

variable [IsNoetherianRing S]

/-- Differential data at level `n`: the map `d_{n+1} : F_{n+1} → F_n`, chosen by covering the
previous syzygy.  Level `0` covers `ker ε ⊆ F₀`; level `n+1` covers `ker dₙ ⊆ F_{n+1}`.  Both
kernels are finite (a submodule of a finite free module over a Noetherian ring), so `coverSub`
applies. -/
noncomputable def diffData : (n : ℕ) → Σ (a b : ℕ), (Fin a → S) →ₗ[S] (Fin b → S)
  | 0 =>
    ⟨(coverSub S (LinearMap.ker (aug S M))).1, augRank S M,
      (coverSub S (LinearMap.ker (aug S M))).2.1⟩
  | n + 1 =>
    ⟨(coverSub S (LinearMap.ker (diffData n).2.2)).1, (diffData n).1,
      (coverSub S (LinearMap.ker (diffData n).2.2)).2.1⟩

/-- Rank of the `n`-th free module `Fₙ = S^{freeRank n}` in the resolution. -/
noncomputable def freeRank (n : ℕ) : ℕ := (diffData S M n).2.1

/-- The `n`-th differential `dₙ : F_{n+1} →ₗ Fₙ` of the finite free resolution. -/
noncomputable def d (n : ℕ) :
    (Fin (freeRank S M (n + 1)) → S) →ₗ[S] (Fin (freeRank S M n) → S) :=
  (diffData S M n).2.2

/-- **Exactness at `F₀`** (Stacks 00LP): the image of the first differential is the kernel of the
augmentation, `range d₀ = ker ε`.  Equivalently, the first syzygy `ker ε` is `range d₀`. -/
theorem range_d_zero : LinearMap.range (d S M 0) = LinearMap.ker (aug S M) :=
  (coverSub S (LinearMap.ker (aug S M))).2.2

/-- **Exactness at `F_{n+1}`** (Stacks 00LP): `range d_{n+1} = ker dₙ`.  Equivalently, the
`(n+2)`-nd syzygy `ker dₙ` is the image `range d_{n+1}`. -/
theorem range_d_succ (n : ℕ) :
    LinearMap.range (d S M (n + 1)) = LinearMap.ker (d S M n) :=
  (coverSub S (LinearMap.ker (d S M n))).2.2

/-- The complex identity at the augmentation: `ε ∘ d₀ = 0`. -/
theorem aug_comp_d_zero : (aug S M) ∘ₗ (d S M 0) = 0 :=
  LinearMap.range_le_ker_iff.mp (le_of_eq (range_d_zero S M))

/-- The complex identity `dₙ ∘ d_{n+1} = 0`: consecutive differentials compose to zero. -/
theorem d_comp_d (n : ℕ) : (d S M n) ∘ₗ (d S M (n + 1)) = 0 :=
  LinearMap.range_le_ker_iff.mp (le_of_eq (range_d_succ S M n))

/-- **The first syzygy `K₁ = ker ε` is finite** (Stacks 00LP). -/
theorem finite_ker_aug : Module.Finite S (LinearMap.ker (aug S M)) := inferInstance

/-- **The `(n+2)`-nd syzygy `K_{n+2} = ker dₙ` is finite** (Stacks 00LP): every syzygy of the
resolution is a finitely generated `S`-module, because it is a submodule of a finite free module
over a Noetherian ring. -/
theorem finite_ker_d (n : ℕ) : Module.Finite S (LinearMap.ker (d S M n)) := inferInstance

/-- The `(n+1)`-st syzygy `K_{n+1}` of the resolution, as a submodule of the free module `Fₙ`
(with the convention `F₋₁ := M`, the map out of `F₀` being the augmentation `ε`):
`syzygy 0 = ker ε = K₁ ⊆ F₀` and `syzygy (n+1) = ker dₙ = K_{n+2} ⊆ F_{n+1}`.  By exactness
(`range_d_zero`, `range_d_succ`) this submodule equals the image of the next differential. -/
noncomputable def syzygy : (n : ℕ) → Σ b : ℕ, Submodule S (Fin b → S)
  | 0 => ⟨augRank S M, LinearMap.ker (aug S M)⟩
  | n + 1 => ⟨freeRank S M (n + 1), LinearMap.ker (d S M n)⟩

/-- **Every syzygy of the resolution is finite** (Stacks 00LP), uniform indexed form:
the `(n+1)`-st syzygy `K_{n+1}` is a finitely generated `S`-module. -/
theorem finite_syzygy (n : ℕ) : Module.Finite S (syzygy S M n).2 := by
  cases n with
  | zero => exact finite_ker_aug S M
  | succ n => exact finite_ker_d S M n

/-- Each resolution term `Fₙ` is a finite `S`-module (it is `S^{freeRank n}`). -/
example (n : ℕ) : Module.Finite S (Fin (freeRank S M n) → S) := inferInstance

/-- Each resolution term `Fₙ` is a free `S`-module. -/
example (n : ℕ) : Module.Free S (Fin (freeRank S M n) → S) := inferInstance

end FiniteFreeResolution
