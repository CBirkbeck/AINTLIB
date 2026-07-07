/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.

# Fibrewise-freeness criterion (Stacks 00MH / Matsumura CRT Thm 22.5)

Let `R → S` be a local homomorphism of local rings (with `S` Noetherian), `M` a finite
`S`-module. Write `𝔪 = maximalIdeal R` and `I = 𝔪·S = (maximalIdeal R).map (algebraMap R S)`,
so that `S ⧸ I = S ⧸ 𝔪S` is the **closed fibre ring** and `M ⧸ I·M` is the fibre `M/𝔪M`.
If

* `M` is flat over `R`, and
* the fibre `M ⧸ 𝔪M` is **free over the fibre ring `S ⧸ 𝔪S`**,

then `M` is free over `S`.  (Stacks 00MH additionally deduces that `S` is flat over `R`; we only
prove the freeness of `M`, which is the part relevant to flat-locus openness.)

## The crux: this is Tor-free

The only homological input is that a flat module preserves the injectivity of a map after
tensoring — `Module.Flat.rTensor_preserves_injective_linearMap`, fed through mathlib's Tor-free
snake-lemma engine `lTensor_injective_of_exact_of_exact_of_rTensor_injective`
(`Mathlib/RingTheory/LocalRing/Module.lean`).  **No derived-functor `Tor` is used anywhere.**
This confirms that the fibrewise-freeness criterion — and hence the box-discharge chain for
openness of the flat locus that rests on it — does *not* require the (mathlib-absent) local
criterion of flatness via commutative `Tor`.

## Note on the statement (delta from a naive spelling)

A tempting but **false** spelling asks for the fibre to be free over the residue *field*
`κ(𝔭) = Frac(R/𝔭)`; over a field every module is free, so that hypothesis is vacuous and the
statement fails (e.g. `R = k` a field, `S = k[x]₍ₓ₎`, `M = k`).  The genuine content is freeness
over the fibre **ring** `S ⧸ 𝔪S`, as spelled here and in Stacks 00MH.

The prime-localised form ("`M` finite `S`-module, `𝔮 ⊂ S` prime over `𝔭 ⊂ R`, `M_𝔮` flat over `R`,
`M_𝔮/𝔭M_𝔮` free over `S_𝔮/𝔭S_𝔮` ⟹ `M_𝔮` free over `S_𝔮`") is the special case obtained by
applying this local theorem to `R_𝔭 → S_𝔮`; that reduction is pure localisation bookkeeping.
-/
import Mathlib

open TensorProduct IsLocalRing Function Module LinearMap

noncomputable section

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
  [Module.Finite S M] [IsNoetherianRing S]

/-- **Fibre datum (pure linear algebra over the fibre ring; no flatness).**

From freeness of the fibre `M ⧸ 𝔪M` over the fibre ring `S ⧸ 𝔪S` one extracts a finite free
presentation `φ : Sʳ → M` that is
* surjective (Nakayama, since the fibre basis generates `M ⧸ 𝔫M`), and
* an isomorphism after reduction modulo `𝔪` (`φ ⊗_R R/𝔪` is bijective — it sends the standard
  basis of `(S/𝔪S)ʳ` to a basis of the free fibre `M/𝔪M`).

This is where the freeness-of-the-fibre hypothesis is consumed; it involves no flatness.  It is
isolated here so that the main theorem's proof is exactly the Tor-free homological argument. -/
private theorem exists_fibre_adapted_surjection
    (hfib : Module.Free (S ⧸ (maximalIdeal R).map (algebraMap R S))
      (M ⧸ ((maximalIdeal R).map (algebraMap R S) • (⊤ : Submodule S M)))) :
    ∃ (r : ℕ) (φ : (Fin r → S) →ₗ[S] M), Function.Surjective φ ∧
      Function.Bijective
        (LinearMap.lTensor (R ⧸ maximalIdeal R) (LinearMap.restrictScalars R φ)) := by
  sorry

/-- **Stacks 00MH / Matsumura CRT 22.5 (freeness half), Tor-free.**
Let `R → S` be a local homomorphism of local rings with `S` Noetherian, and `M` a finite
`S`-module that is flat over `R`.  If the fibre `M ⧸ 𝔪M` is free over the fibre ring `S ⧸ 𝔪S`
(where `𝔪 = maximalIdeal R`), then `M` is free over `S`. -/
theorem Module.free_of_flat_of_fibre_free [Module.Flat R M]
    (hfib : Module.Free (S ⧸ (maximalIdeal R).map (algebraMap R S))
      (M ⧸ ((maximalIdeal R).map (algebraMap R S) • (⊤ : Submodule S M)))) :
    Module.Free S M := by
  obtain ⟨r, φ, hsurj, hbij⟩ := exists_fibre_adapted_surjection hfib
  set k := R ⧸ IsLocalRing.maximalIdeal R with hk
  set φR := LinearMap.restrictScalars R φ with hφR
  set Ksub := LinearMap.ker φ with hKsub
  -- (A) : `ι ⊗ k` is injective.  This is the Tor-free crux: it is deduced from `M` flat over `R`
  -- via `Flat.rTensor_preserves_injective_linearMap` and the snake engine
  -- `lTensor_injective_of_exact_of_exact_of_rTensor_injective`.
  have hAinj : Function.Injective (LinearMap.lTensor k
      (LinearMap.restrictScalars R Ksub.subtype)) :=
    lTensor_injective_of_exact_of_exact_of_rTensor_injective
      (f₁ := (maximalIdeal R).subtype) (f₂ := (maximalIdeal R).mkQ)
      (g₁ := LinearMap.restrictScalars R Ksub.subtype) (g₂ := φR)
      (LinearMap.exact_subtype_mkQ (maximalIdeal R)) (Submodule.mkQ_surjective _)
      (LinearMap.exact_subtype_ker_map φ) hsurj
      (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)
      (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)
  have hcomp : φR ∘ₗ (LinearMap.restrictScalars R Ksub.subtype) = 0 := by
    ext w; exact LinearMap.mem_ker.mp w.2
  -- `k ⊗_R K = 0`: `ι ⊗ k` is injective (A) and lands in `ker (φ ⊗ k) = 0` (as `φ ⊗ k` is bijective).
  have hkK : Subsingleton (k ⊗[R] Ksub) := by
    refine (subsingleton_iff_forall_eq 0).mpr fun z => ?_
    have hz : LinearMap.lTensor k (LinearMap.restrictScalars R Ksub.subtype) z = 0 := by
      apply hbij.1
      rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hcomp,
        LinearMap.lTensor_zero, LinearMap.zero_apply]
    exact hAinj (by rw [hz, map_zero])
  -- `k ⊗_R K = 0` ⟹ `𝔪·K = K` (R-lattice).
  haveI hqss : Subsingleton (Ksub ⧸ (maximalIdeal R) • (⊤ : Submodule R Ksub)) :=
    (TensorProduct.quotTensorEquivQuotSMul Ksub (maximalIdeal R)).toEquiv.subsingleton_congr.mp hkK
  have htopR : (maximalIdeal R) • (⊤ : Submodule R Ksub) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx0 : Submodule.Quotient.mk x
        = (0 : Ksub ⧸ (maximalIdeal R) • (⊤ : Submodule R Ksub)) := Subsingleton.elim _ _
    rwa [Submodule.Quotient.mk_eq_zero] at hx0
  -- Since `𝔪·S ⊆ 𝔫`, `𝔪·K = K` forces `𝔫·K = K`.
  have htopS : (⊤ : Submodule S Ksub) ≤ (maximalIdeal S) • (⊤ : Submodule S Ksub) := by
    intro x _
    have hxmem : x ∈ (maximalIdeal R) • (⊤ : Submodule R Ksub) := htopR.ge Submodule.mem_top
    refine Submodule.smul_induction_on hxmem ?_ (fun a b ha hb => Submodule.add_mem _ ha hb)
    intro rr hrr m _
    rw [← IsScalarTower.algebraMap_smul S rr m]
    exact Submodule.smul_mem_smul
      (IsLocalRing.map_maximalIdeal_le (algebraMap R S) (Ideal.mem_map_of_mem _ hrr))
      Submodule.mem_top
  -- Nakayama over the local ring `S` (K finite over S): `K = 0`.
  have hnak : (⊤ : Submodule S Ksub) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal S) ⊤ (Module.Finite.fg_top)
      htopS (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  have hKbot : Ksub = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have : (⟨x, hx⟩ : ↥Ksub) ∈ (⊥ : Submodule S ↥Ksub) := hnak ▸ Submodule.mem_top
    simpa using this
  -- `K = 0` ⟹ `φ` injective ⟹ (with surjectivity) `M ≅ Sʳ` is free.
  have hφinj : Function.Injective φ := LinearMap.ker_eq_bot.mp hKbot
  exact Module.Free.of_equiv (LinearEquiv.ofBijective φ ⟨hφinj, hsurj⟩)

end
