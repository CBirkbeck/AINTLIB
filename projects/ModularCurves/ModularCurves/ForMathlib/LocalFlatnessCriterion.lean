/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.

# Local criterion of flatness for a cokernel (Stacks 00ME, flatness half — standalone)

Let `(R, 𝔪)` be a Noetherian local ring, `N` a finite `R`-module, `M` a flat `R`-module, and
`u : N →ₗ[R] M`.  Write `ū_I : N/IN → M/IM` for the reduction of `u` modulo an ideal `I`.  If

* the residue-field fibre `ū_𝔪 : N/𝔪N → M/𝔪M` is **injective**,

then the cokernel `M ⧸ u(N)` is **flat over `R`**.  This is the flatness content of Stacks 00ME
(Lemma 10.99.1), extracted so that it is *independent* of the Buchsbaum–Eisenbud acyclicity
machinery (`ModularCurves.ForMathlib.BuchsbaumEisenbud`).

## Proof architecture

The argument splits into two mathematically distinct pieces:

1. **`coker_flat_of_fibre_injective_forall` (pure homological algebra, no sorry).**
   *If `ū_I` is injective for **every** finitely generated ideal `I`, then `M ⧸ u(N)` is flat.*
   By the ideal criterion for flatness (`Module.Flat.iff_lTensor_injective`) it suffices to check,
   for each f.g. ideal `I`, that `I ⊗ (M/u(N)) → R ⊗ (M/u(N))` is injective.  Applying mathlib's
   tensor four-lemma `lTensor_injective_of_exact_of_exact_of_rTensor_injective` to the two right-exact
   rows
   ```
       N  →u→  M  →π→  M/u(N)  → 0            (π = (range u).mkQ)
       I  →⊆→  R  →→   R/I      → 0
   ```
   reduces this to two injectivities: `u ⊗ (R/I)` injective (this is `ū_I`, the hypothesis) and
   `I ⊗ M → R ⊗ M` injective (this is exactly flatness of `M`).  No local criterion is used here.

2. **`fibre_injective_of_maximal` (the local criterion of flatness — the one hard step, `sorry`).**
   *`ū_𝔪` injective ⟹ `ū_I` injective for every f.g. ideal `I`.*  This is the genuine
   local-criterion-of-flatness content (Stacks 00MK, Matsumura *Commutative Ring Theory* Thm 22.3):
   the finiteness of `N` over the Noetherian local ring `R` feeds the Artin–Rees lemma
   (`Ideal.exists_pow_inf_eq_pow_smul`) / Krull-intersection bootstrap that propagates injectivity
   from the special fibre `I = 𝔪` to all finitely generated `I`.

The main theorem `coker_of_flat_of_fibre_injective` is the composition `1 ∘ 2`.

## Note on hypotheses (delta from Stacks 00ME)

Stacks 00ME is stated for a local homomorphism `R → S` of Noetherian local rings with `N`, `M`
finite `S`-modules.  Here we prove the **`R`-substrate**: `N` is finite over `R` itself and `M` is
merely `R`-flat (not necessarily finite).  This is the form needed to bridge scalars to the
`S`-algebra version; the finiteness that the Artin–Rees bootstrap actually consumes is that of `N`.
-/
import Mathlib

open TensorProduct Function

namespace Module.Flat

variable {R N M : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [AddCommGroup N] [Module R N] [Module.Finite R N]
  [AddCommGroup M] [Module R M] [Module.Flat R M]

omit [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R N] in
/-- **The reduction (pure homological algebra; no local criterion).**

If the reduced map `ū_I : N/IN → M/IM` (i.e. `LinearMap.lTensor (R ⧸ I) u`) is injective for every
finitely generated ideal `I`, then the cokernel `M ⧸ u(N)` is flat over `R`.

This is proved from the ideal criterion for flatness together with mathlib's tensor four-lemma
`lTensor_injective_of_exact_of_exact_of_rTensor_injective`, using only that `M` is flat.  It does
**not** use Noetherianity, locality, or finiteness of `N` (those are needed only to *establish* the
hypothesis, in `fibre_injective_of_maximal`). -/
theorem coker_flat_of_fibre_injective_forall (u : N →ₗ[R] M)
    (hI : ∀ ⦃I : Ideal R⦄, I.FG → Function.Injective (LinearMap.lTensor (R ⧸ I) u)) :
    Module.Flat R (M ⧸ LinearMap.range u) := by
  rw [Module.Flat.iff_lTensor_injective]
  intro I hIfg
  -- Tensor four-lemma on the two right-exact rows `N →u→ M →π→ Q → 0` and `I → R → R/I → 0`.
  refine lTensor_injective_of_exact_of_exact_of_rTensor_injective
    (f₁ := u) (f₂ := (LinearMap.range u).mkQ)
    (g₁ := I.subtype) (g₂ := Submodule.mkQ I) ?_ ?_ ?_ ?_ ?_ ?_
  · -- `N →u→ M →π→ Q` is exact: `range u = ker π`.
    exact LinearMap.exact_iff.mpr (Submodule.ker_mkQ _)
  · -- `π = (range u).mkQ` is surjective.
    exact Submodule.mkQ_surjective _
  · -- `I → R → R/I` is exact.
    exact LinearMap.exact_subtype_mkQ I
  · -- `R → R/I` is surjective.
    exact Submodule.mkQ_surjective I
  · -- `u ⊗ (R/I) : N ⊗ (R/I) → M ⊗ (R/I)` is injective: this is `ū_I` (the hypothesis).
    exact (u.lTensor_inj_iff_rTensor_inj (R ⧸ I)).mp (hI hIfg)
  · -- `I ⊗ M → R ⊗ M` is injective: this is exactly flatness of `M`.
    exact Module.Flat.iff_lTensor_injective'.mp inferInstance I

/-- **The local criterion of flatness (Stacks 00MK / Matsumura Thm 22.3) — THE hard step.**

Over a Noetherian local ring `R`, with `N` finite and `M` flat, injectivity of the special-fibre
reduction `ū_𝔪 : N/𝔪N → M/𝔪M` propagates to injectivity of `ū_I : N/IN → M/IM` for **every**
finitely generated ideal `I`.

MISSING FACT (the single sorry): this is the local-criterion-of-flatness bootstrap.  With `N` finite
over the Noetherian local ring `R`, the Artin–Rees lemma (`Ideal.exists_pow_inf_eq_pow_smul`) and the
Krull-intersection theorem (`Ideal.iInf_pow_smul_eq_bot_of_isLocalRing`) control the `𝔪`-adic
filtration on `N` and on `K = ker u`, upgrading the special-fibre injectivity `ū_𝔪` to `ū_I` for all
`I`.  See Matsumura, *Commutative Ring Theory*, Theorem 22.3, and Stacks tag 00MK.  The flatness of
`M` is used to identify `IM` with `I ⊗ M` throughout the induction. -/
theorem fibre_injective_of_maximal (u : N →ₗ[R] M)
    (hbar : Function.Injective (LinearMap.lTensor (R ⧸ IsLocalRing.maximalIdeal R) u)) :
    ∀ ⦃I : Ideal R⦄, I.FG → Function.Injective (LinearMap.lTensor (R ⧸ I) u) := by
  sorry

/-- **Stacks 00ME (Lemma 10.99.1), flatness half — standalone.**

`R` Noetherian local, `N` a finite `R`-module, `M` a flat `R`-module, `u : N →ₗ[R] M` with the
residue-field fibre `ū_𝔪 : N/𝔪N → M/𝔪M` injective ⟹ the cokernel `M ⧸ u(N)` is flat over `R`. -/
theorem coker_of_flat_of_fibre_injective (u : N →ₗ[R] M)
    (hbar : Function.Injective
      (LinearMap.lTensor (R ⧸ IsLocalRing.maximalIdeal R) u)) :
    Module.Flat R (M ⧸ LinearMap.range u) :=
  coker_flat_of_fibre_injective_forall u (fibre_injective_of_maximal u hbar)

end Module.Flat
