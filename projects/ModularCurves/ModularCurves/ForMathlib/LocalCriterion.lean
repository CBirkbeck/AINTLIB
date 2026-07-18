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
import Mathlib.RingTheory.LocalRing.Module

open TensorProduct IsLocalRing Function Module LinearMap

noncomputable section

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
  [Module.Finite S M] [IsNoetherianRing S]

section FibreBaseChange

variable (N : Type*) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

omit [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]

/-- For an `S`-module `N`, restricting the `S`-submodule `𝔞S·N` (generated over `S` by an ideal
`𝔞` of `R`) back to `R` recovers the `R`-submodule `𝔞·N`.  Combines `Ideal.smul_restrictScalars`
with `Submodule.restrictScalars_top`. -/
theorem restrictScalars_map_smul_top (𝔞 : Ideal R) :
    (𝔞.map (algebraMap R S) • (⊤ : Submodule S N)).restrictScalars R
      = 𝔞 • (⊤ : Submodule R N) := by
  rw [Ideal.smul_restrictScalars, Submodule.restrictScalars_top]

/-- **Fibre base change.** For an ideal `𝔞` of `R` and an `S`-module `N`, the base change
`(R ⧸ 𝔞) ⊗[R] N` is `R`-linearly identified with the fibre quotient `N ⧸ 𝔞S·N`.  It is
`TensorProduct.quotTensorEquivQuotSMul` (which lands in the `R`-submodule quotient `N ⧸ 𝔞·N`)
composed with the identification `𝔞·N = (𝔞S·N)↾R` of `restrictScalars_map_smul_top`. -/
noncomputable def quotTensorEquivQuotMapSMul (𝔞 : Ideal R) :
    (R ⧸ 𝔞) ⊗[R] N ≃ₗ[R] N ⧸ (𝔞.map (algebraMap R S) • (⊤ : Submodule S N)) :=
  TensorProduct.quotTensorEquivQuotSMul N 𝔞 ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (restrictScalars_map_smul_top N 𝔞).symm ≪≫ₗ
    Submodule.Quotient.restrictScalarsEquiv R _

theorem quotTensorEquivQuotMapSMul_mk_tmul (𝔞 : Ideal R) (a : R) (v : N) :
    quotTensorEquivQuotMapSMul N 𝔞 (Ideal.Quotient.mk 𝔞 a ⊗ₜ[R] v)
      = (Submodule.Quotient.mk (a • v) :
          N ⧸ (𝔞.map (algebraMap R S) • (⊤ : Submodule S N))) := by
  simp only [quotTensorEquivQuotMapSMul, LinearEquiv.trans_apply,
    TensorProduct.quotTensorEquivQuotSMul_mk_tmul, Submodule.quotEquivOfEq_mk,
    Submodule.Quotient.restrictScalarsEquiv_mk]

end FibreBaseChange

omit [IsNoetherianRing S] in
/-- **Fibre datum (pure linear algebra over the fibre ring; no flatness).**

From freeness of the fibre `M ⧸ 𝔪M` over the fibre ring `S ⧸ 𝔪S` one extracts a finite free
presentation `φ : Sʳ → M` that is
* surjective (Nakayama, since the fibre basis generates `M ⧸ 𝔫M`), and
* injective after reduction modulo `𝔪` (`φ ⊗_R R/𝔪` is injective — indeed an isomorphism, as it
  sends the standard basis of `(S/𝔪S)ʳ` to the basis of the free fibre `M/𝔪M`).

This is where the freeness-of-the-fibre hypothesis is consumed; it involves no flatness.  It is
isolated here so that the main theorem's proof is exactly the Tor-free homological argument. -/
private theorem exists_fibre_adapted_surjection
    (hfib : Module.Free (S ⧸ (maximalIdeal R).map (algebraMap R S))
      (M ⧸ ((maximalIdeal R).map (algebraMap R S) • (⊤ : Submodule S M)))) :
    ∃ (r : ℕ) (φ : (Fin r → S) →ₗ[S] M), Function.Surjective φ ∧
      Function.Injective
        (LinearMap.lTensor (R ⧸ maximalIdeal R) (LinearMap.restrictScalars R φ)) := by
  classical
  set I : Ideal S := (maximalIdeal R).map (algebraMap R S) with hI
  haveI hfree : Module.Free (S ⧸ I) (M ⧸ (I • (⊤ : Submodule S M))) := hfib
  -- surjectivity of the residue map `S → S ⧸ I`
  have hSsurj : Function.Surjective (algebraMap S (S ⧸ I)) := by
    rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective
  -- fibre basis, reindexed to `Fin r`
  obtain ⟨r, b⟩ : Σ' (r : ℕ), Basis (Fin r) (S ⧸ I) (M ⧸ (I • (⊤ : Submodule S M))) :=
    ⟨_, (Module.Free.chooseBasis (S ⧸ I) (M ⧸ (I • (⊤ : Submodule S M)))).reindex
      (Fintype.equivFin _)⟩
  -- lift the basis to `M`
  choose x hx using fun i => Submodule.Quotient.mk_surjective (I • (⊤ : Submodule S M)) (b i)
  set φ : (Fin r → S) →ₗ[S] M := Fintype.linearCombination S x with hφ_def
  have hφsingle : ∀ i, φ (Pi.single i (1 : S)) = x i := by
    intro i; rw [hφ_def, Fintype.linearCombination_apply_single, one_smul]
  have hb_span : Submodule.span S (Set.range ⇑b) = ⊤ := by
    rw [← Submodule.restrictScalars_span S (S ⧸ I) hSsurj (Set.range ⇑b), b.span_eq,
      Submodule.restrictScalars_top]
  refine ⟨r, φ, ?_, ?_⟩
  · -- `φ` surjective, by Nakayama at `I` (the lifted basis generates `M ⧸ IM`)
    rw [← LinearMap.range_eq_top, hφ_def, Fintype.range_linearCombination]
    have hfeq : ⇑(I • (⊤ : Submodule S M)).mkQ ∘ x = ⇑b := funext (fun i => hx i)
    have hgenI : Submodule.map (I • (⊤ : Submodule S M)).mkQ
        (Submodule.span S (Set.range x)) = ⊤ := by
      rw [Submodule.map_span, ← Set.range_comp, hfeq]; exact hb_span
    have hNN : (⊤ : Submodule S M) ≤ Submodule.span S (Set.range x) ⊔ I • (⊤ : Submodule S M) := by
      have h2 : (I • (⊤ : Submodule S M)) ⊔ Submodule.span S (Set.range x) = ⊤ :=
        (Submodule.map_mkQ_eq_top (I • (⊤ : Submodule S M))
          (Submodule.span S (Set.range x))).mp hgenI
      rw [sup_comm] at h2; exact h2.ge
    have hnak := Submodule.le_of_le_smul_of_le_jacobson_bot (I := I)
      (N := Submodule.span S (Set.range x)) (N' := (⊤ : Submodule S M))
      Module.Finite.fg_top
      (by rw [hI, IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal S) bot_ne_top]
          exact IsLocalRing.map_maximalIdeal_le (algebraMap R S)) hNN
    exact top_le_iff.mp hnak
  · -- `φ ⊗_R (R/𝔪)` injective: it is conjugate to the fibre reduction `ψ`, which is an iso.
    -- `R`-linear identifications  `(R/𝔪) ⊗[R] N ≃ N ⧸ IN` (fibre base change)
    set eM : (R ⧸ maximalIdeal R) ⊗[R] M ≃ₗ[R] M ⧸ (I • (⊤ : Submodule S M)) :=
      quotTensorEquivQuotMapSMul M (maximalIdeal R) with heM
    set eN : (R ⧸ maximalIdeal R) ⊗[R] (Fin r → S) ≃ₗ[R]
        (Fin r → S) ⧸ (I • (⊤ : Submodule S (Fin r → S))) :=
      quotTensorEquivQuotMapSMul (Fin r → S) (maximalIdeal R) with heN
    -- the descended `S`-linear reduction `ψ`
    have hφle : (I • (⊤ : Submodule S (Fin r → S))) ≤
        Submodule.comap φ (I • (⊤ : Submodule S M)) := by
      rw [Submodule.smul_le]
      intro a ha v _
      rw [Submodule.mem_comap, map_smul]
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    set ψ : ((Fin r → S) ⧸ (I • (⊤ : Submodule S (Fin r → S)))) →ₗ[S]
        (M ⧸ (I • (⊤ : Submodule S M))) := Submodule.mapQ _ _ φ hφle with hψ_def
    -- naturality: `eM ∘ (φ ⊗ k) = ψ ∘ eN`
    have hnat : ∀ z, eM (LinearMap.lTensor (R ⧸ maximalIdeal R) (LinearMap.restrictScalars R φ) z)
        = ψ (eN z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a v =>
          obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
          rw [heM, heN, hψ_def, LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply,
            quotTensorEquivQuotMapSMul_mk_tmul, quotTensorEquivQuotMapSMul_mk_tmul,
            Submodule.mapQ_apply]
          rw [φ.map_smul_of_tower a' v]
      | add z1 z2 h1 h2 => simp only [map_add, h1, h2]
    -- standard `S⧸I`-basis of the source quotient
    set c : Basis (Fin r) (S ⧸ I) ((Fin r → S) ⧸ (I • (⊤ : Submodule S (Fin r → S)))) :=
      (Basis.baseChange (S ⧸ I) (Pi.basisFun S (Fin r))).map
        ((quotTensorEquivQuotSMul (Fin r → S) I).extendScalarsOfSurjective hSsurj) with hc_def
    have hc : ∀ i, c i = Submodule.Quotient.mk (Pi.single i (1 : S)) := by
      intro i
      rw [hc_def]
      simp only [Basis.map_apply, Basis.baseChange_apply, Pi.basisFun_apply,
        LinearEquiv.extendScalarsOfSurjective_apply]
      rw [show (1 : S ⧸ I) = Ideal.Quotient.mk I 1 from (map_one _).symm,
        quotTensorEquivQuotSMul_mk_tmul, one_smul]
    -- `S⧸I`-linear upgrade of `ψ`; it sends the basis `c` to the basis `b`, hence is an iso
    set ψbar := ψ.extendScalarsOfSurjective hSsurj with hψbar_def
    have hbar_key : ∀ i, ψbar (c i) = b i := by
      intro i
      rw [hc i, hψbar_def, LinearMap.extendScalarsOfSurjective_apply, hψ_def,
        Submodule.mapQ_apply, hφsingle i]
      exact hx i
    have hbar_eq : ψbar = (c.equiv b (Equiv.refl (Fin r))).toLinearMap := by
      apply c.ext
      intro i
      rw [hbar_key i]
      simp [Basis.equiv_apply]
    have hψinj : Function.Injective ⇑ψ := by
      have hbi : Function.Injective ⇑ψbar := by
        rw [hbar_eq]; exact (c.equiv b (Equiv.refl (Fin r))).injective
      intro a1 a2 h
      apply hbi
      rw [hψbar_def, LinearMap.extendScalarsOfSurjective_apply,
        LinearMap.extendScalarsOfSurjective_apply]
      exact h
    intro z1 z2 hz
    apply eN.injective
    apply hψinj
    rw [← hnat z1, ← hnat z2, hz]

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
  -- `k ⊗_R K = 0`: `ι ⊗ k` is injective (A) and lands in `ker (φ ⊗ k) = 0`
  -- (as `φ ⊗ k` is injective).
  have hkK : Subsingleton (k ⊗[R] Ksub) := by
    refine (subsingleton_iff_forall_eq 0).mpr fun z => ?_
    have hz : LinearMap.lTensor k (LinearMap.restrictScalars R Ksub.subtype) z = 0 := by
      apply hbij
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
