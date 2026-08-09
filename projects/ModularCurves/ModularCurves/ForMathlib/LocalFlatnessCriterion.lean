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

2. **`fibre_injective_of_maximal` (the local criterion of flatness — the one hard step).**
   *`ū_𝔪` injective ⟹ `ū_I` injective for every f.g. ideal `I`.*  This is the genuine
   local-criterion-of-flatness content (Stacks 00MK, Matsumura *Commutative Ring Theory* Thm 22.3).
   The engine is the residue-field core `injective_of_lTensor_residueField_injective`: over a local
   ring, `M` flat and `N` finite, injectivity of the residue-field fibre `k ⊗ u` forces `u` itself to
   be injective (minimal generators from a residue-field basis, made `R`-independent by
   `IsLocalRing.linearIndependent_of_flat`).  For a proper f.g. `I`, base-change to the local ring
   `R ⧸ I` turns `ū_I` into `u' = (R ⧸ I) ⊗ u`, whose residue-field fibre is identified with `ū_𝔪`
   by two `cancelBaseChange` naturality steps; the core then gives `u'` injective.  (No Artin–Rees or
   Krull-intersection bootstrap is needed.)

The main theorem `coker_of_flat_of_fibre_injective` is the composition `1 ∘ 2`.

## Note on hypotheses (delta from Stacks 00ME)

Stacks 00ME is stated for a local homomorphism `R → S` of Noetherian local rings with `N`, `M`
finite `S`-modules.  Here we prove the **`R`-substrate**: `N` is finite over `R` itself and `M` is
merely `R`-flat (not necessarily finite).  This is the form needed to bridge scalars to the
`S`-algebra version; the finiteness that the residue-field core actually consumes is that of `N`.
-/
import Mathlib

-- v4.33 bump: neither the category instances nor the semireducible component types are
-- transparent enough for the rewrites and instance searches below.
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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

omit [IsNoetherianRing R] in
/-- **Local criterion of flatness — the residue-field core.**

Over a Noetherian local ring `R` with `N` finite and `M` flat, if the residue-field fibre
`k ⊗ u : k ⊗ N → k ⊗ M` (with `k = IsLocalRing.ResidueField R`) is injective, then `u` itself is
injective.

Proof: lift a `k`-basis `w` of `k ⊗ N` to a family `v` in `N` (minimal generators), exactly as in
`Module.free_of_flat_of_isLocalRing`.  Injectivity of the fibre makes
`(baseChange k u) ∘ w = k ⊗ (u ∘ v)` linearly independent over `k`, so by
`IsLocalRing.linearIndependent_of_flat` (this is where flatness of `M` enters) the family `u ∘ v` is
linearly independent over `R`.  As `v` generates `N` (`IsLocalRing.span_eq_top_of_tmul_eq_basis`),
`Finsupp.linearCombination R v` is surjective, while `Finsupp.linearCombination R (u ∘ v) =
u ∘ₗ Finsupp.linearCombination R v` is injective; together these force `u` injective. -/
theorem injective_of_lTensor_residueField_injective (u : N →ₗ[R] M)
    (hbar : Function.Injective (LinearMap.lTensor (IsLocalRing.ResidueField R) u)) :
    Function.Injective u := by
  classical
  -- A `k`-basis of `k ⊗ N`, lifted (via surjectivity of `n ↦ 1 ⊗ n`) to a family `v` in `N`.
  let w := Module.Free.chooseBasis (IsLocalRing.ResidueField R)
    (IsLocalRing.ResidueField R ⊗[R] N)
  obtain ⟨v, hv⟩ := (TensorProduct.mk_surjective R N (IsLocalRing.ResidueField R)
    Ideal.Quotient.mk_surjective).comp_left w
  -- `hbar` says `k ⊗ u`, equivalently `baseChange k u`, is injective.
  have hbar' : Function.Injective ⇑(LinearMap.baseChange (IsLocalRing.ResidueField R) u) := by
    rw [LinearMap.baseChange_eq_ltensor]; exact hbar
  -- Hence `k ⊗ (u ∘ v) = (baseChange k u) ∘ w` is `k`-linearly independent…
  have hli : LinearIndependent (IsLocalRing.ResidueField R)
      (TensorProduct.mk R (IsLocalRing.ResidueField R) M 1 ∘ (⇑u ∘ v)) := by
    have key : (TensorProduct.mk R (IsLocalRing.ResidueField R) M 1) ∘ (⇑u ∘ v)
        = ⇑(LinearMap.baseChange (IsLocalRing.ResidueField R) u) ∘ ⇑w := by
      rw [← hv]; ext i; simp
    rw [key]
    exact w.linearIndependent.map' _ (LinearMap.ker_eq_bot.mpr hbar')
  -- …so `u ∘ v` is `R`-linearly independent (flatness of `M`).
  have hui : LinearIndependent R (⇑u ∘ v) := IsLocalRing.linearIndependent_of_flat _ hli
  -- `v` generates `N`, so `Finsupp.linearCombination R v` is surjective.
  have hspan : Submodule.span R (Set.range v) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis v w (congr_fun hv)
  have hsurj : Function.Surjective (Finsupp.linearCombination R v) :=
    LinearMap.range_eq_top.mp (by rw [Finsupp.range_linearCombination, hspan])
  -- `Finsupp.linearCombination R (u ∘ v) = u ∘ₗ Finsupp.linearCombination R v` is injective, and its
  -- second factor is surjective; therefore `u` is injective.
  have hui_inj : Function.Injective ⇑(u ∘ₗ Finsupp.linearCombination R v) := by
    rw [← Finsupp.linearCombination_linear_comp R u]; exact hui
  intro x y hxy
  obtain ⟨a, rfl⟩ := hsurj x
  obtain ⟨b, rfl⟩ := hsurj y
  exact congrArg (Finsupp.linearCombination R v) (hui_inj hxy)

/-- Injectivity transfer across a commuting square `p ∘ eN = eM ∘ q` with `eN` injective:
if the top map `p` is injective then so is the bottom map `q`. -/
private theorem injective_of_comm_sq {A B C D : Type*} {p : B → D} {q : A → C}
    {eN : A → B} {eM : C → D} (heq : p ∘ eN = eM ∘ q) (heN : Function.Injective eN)
    (hp : Function.Injective p) : Function.Injective q :=
  (heq ▸ hp.comp heN).of_comp

/-- Injectivity transfer across a commuting square `p ∘ eN = eM ∘ q` with `eN` surjective and `eM`
injective: if the bottom map `q` is injective then so is the top map `p`. -/
private theorem injective_of_comm_sq' {A B C D : Type*} {p : B → D} {q : A → C}
    {eN : A → B} {eM : C → D} (heq : p ∘ eN = eM ∘ q) (heN : Function.Surjective eN)
    (heM : Function.Injective eM) (hq : Function.Injective q) : Function.Injective p := by
  have h1 : Function.Injective (p ∘ eN) := by rw [heq]; exact heM.comp hq
  intro a b hab
  obtain ⟨x, rfl⟩ := heN a
  obtain ⟨y, rfl⟩ := heN b
  exact congrArg eN (h1 hab)

open TensorProduct.AlgebraTensorModule in
/-- **The local criterion of flatness (Stacks 00MK / Matsumura Thm 22.3) — THE hard step.**

Over a Noetherian local ring `R`, with `N` finite and `M` flat, injectivity of the special-fibre
reduction `ū_𝔪 : N/𝔪N → M/𝔪M` propagates to injectivity of `ū_I : N/IN → M/IM` for **every**
finitely generated ideal `I`.

Proof.  For `I = ⊤` the source `(R ⧸ ⊤) ⊗ N` is a subsingleton, so `ū_⊤` is injective.  For `I ≠ ⊤`
the ring `R' = R ⧸ I` is again Noetherian local (`I ≤ 𝔪`), the base changes `R' ⊗ N` and `R' ⊗ M`
are respectively finite and flat over `R'`, and `ū_I` is (the underlying map of) the `R'`-linear
base change `u' = R' ⊗ u`.  So it suffices, by the residue-field core
`injective_of_lTensor_residueField_injective` applied over `R'`, to check that the residue-field
fibre of `u'` over `R'` — a map tensored up to `k' = ResidueField R'` — is injective.  Two
applications of `AlgebraTensorModule.cancelBaseChange` naturality
(`lTensor_comp_cancelBaseChange`), along the towers `R → R ⧸ 𝔪 → k'` and `R → R' → k'`, identify
this residue-field fibre with `k' ⊗ ū_𝔪` (base change of `hbar` along the field extension
`ResidueField R → k'`), which is injective because `hbar` is and `k'` is flat over the field
`ResidueField R`.  See Matsumura, *Commutative Ring Theory*, Theorem 22.3, and Stacks tag 00MK. -/
theorem fibre_injective_of_maximal (u : N →ₗ[R] M)
    (hbar : Function.Injective (LinearMap.lTensor (R ⧸ IsLocalRing.maximalIdeal R) u)) :
    ∀ ⦃I : Ideal R⦄, I.FG → Function.Injective (LinearMap.lTensor (R ⧸ I) u) := by
  intro I _
  rcases eq_or_ne I ⊤ with rfl | hI_ne
  · -- `I = ⊤`: `R ⧸ ⊤` is the zero ring, so the whole domain `(R ⧸ ⊤) ⊗ N` is a subsingleton.
    haveI : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    haveI : Subsingleton ((R ⧸ (⊤ : Ideal R)) ⊗[R] N) := Module.subsingleton (R ⧸ (⊤ : Ideal R)) _
    exact Function.injective_of_subsingleton _
  · -- `I ≠ ⊤`: base-change to the Noetherian local ring `R' = R ⧸ I` (with `M`-base-change flat and
    -- `N`-base-change finite) and apply the residue-field core `L` to `u' = baseChange (R ⧸ I) u`.
    haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI_ne
    haveI : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    haveI : IsLocalHom (Ideal.Quotient.mk I) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    -- The residue-field fibre of `u' = baseChange (R ⧸ I) u`, over `R ⧸ I`, is injective (`= hbar`).
    have hbar'' : Function.Injective (LinearMap.lTensor (IsLocalRing.ResidueField (R ⧸ I))
        (LinearMap.baseChange (R ⧸ I) u)) := by
      -- `hbar` says `ū_𝔪 = baseChange (ResidueField R) u` is injective.
      have hbarBC : Function.Injective ⇑(LinearMap.baseChange (IsLocalRing.ResidueField R) u) := by
        rw [LinearMap.baseChange_eq_ltensor]; exact hbar
      -- Tensoring up to the field extension `ResidueField R → k'` keeps it injective (`k'` flat).
      have hBfield : Function.Injective ⇑(LinearMap.lTensor (IsLocalRing.ResidueField (R ⧸ I))
          (LinearMap.baseChange (IsLocalRing.ResidueField R) u)) :=
        Module.Flat.lTensor_preserves_injective_linearMap _ hbarBC
      -- Naturality of `cancelBaseChange` along `R → ResidueField R → k'`: identify `k' ⊗ ū_𝔪` with
      -- the `R`-base change `k' ⊗ u`, giving injectivity of the latter.
      have eqB := lTensor_comp_cancelBaseChange R (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField (R ⧸ I)) (M := IsLocalRing.ResidueField (R ⧸ I))
        (N := N) (Q := M) u
      have eqBf : ⇑(LinearMap.lTensor (IsLocalRing.ResidueField (R ⧸ I)) u)
            ∘ ⇑(cancelBaseChange R (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField (R ⧸ I))
                  (IsLocalRing.ResidueField (R ⧸ I)) N)
          = ⇑(cancelBaseChange R (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField (R ⧸ I))
                  (IsLocalRing.ResidueField (R ⧸ I)) M)
            ∘ ⇑(LinearMap.lTensor (IsLocalRing.ResidueField (R ⧸ I))
                  (lTensor (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R) u)) := by
        simpa only [LinearMap.coe_comp, coe_lTensor, LinearEquiv.coe_coe]
          using congrArg DFunLike.coe eqB
      have hStepB : Function.Injective ⇑(LinearMap.lTensor (IsLocalRing.ResidueField (R ⧸ I)) u) :=
        injective_of_comm_sq' eqBf
          (cancelBaseChange R (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField (R ⧸ I))
            (IsLocalRing.ResidueField (R ⧸ I)) N).surjective
          (cancelBaseChange R (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField (R ⧸ I))
            (IsLocalRing.ResidueField (R ⧸ I)) M).injective hBfield
      -- Naturality of `cancelBaseChange` along `R → R ⧸ I → k'`: identify `k' ⊗ u` with the
      -- residue-field fibre of `u' = R' ⊗ u`, transporting injectivity to `hbar''`.
      have eqA := lTensor_comp_cancelBaseChange R (R ⧸ I)
        (IsLocalRing.ResidueField (R ⧸ I)) (M := IsLocalRing.ResidueField (R ⧸ I))
        (N := N) (Q := M) u
      have eqAf : ⇑(LinearMap.lTensor (IsLocalRing.ResidueField (R ⧸ I)) u)
            ∘ ⇑(cancelBaseChange R (R ⧸ I) (IsLocalRing.ResidueField (R ⧸ I))
                  (IsLocalRing.ResidueField (R ⧸ I)) N)
          = ⇑(cancelBaseChange R (R ⧸ I) (IsLocalRing.ResidueField (R ⧸ I))
                  (IsLocalRing.ResidueField (R ⧸ I)) M)
            ∘ ⇑(LinearMap.lTensor (IsLocalRing.ResidueField (R ⧸ I))
                  (lTensor (R ⧸ I) (R ⧸ I) u)) := by
        simpa only [LinearMap.coe_comp, coe_lTensor, LinearEquiv.coe_coe]
          using congrArg DFunLike.coe eqA
      exact injective_of_comm_sq eqAf
        (cancelBaseChange R (R ⧸ I) (IsLocalRing.ResidueField (R ⧸ I))
          (IsLocalRing.ResidueField (R ⧸ I)) N).injective hStepB
    have hinj : Function.Injective ⇑(LinearMap.baseChange (R ⧸ I) u) :=
      injective_of_lTensor_residueField_injective _ hbar''
    rwa [LinearMap.baseChange_eq_ltensor] at hinj

/-- **Stacks 00ME (Lemma 10.99.1), flatness half — standalone.**

`R` Noetherian local, `N` a finite `R`-module, `M` a flat `R`-module, `u : N →ₗ[R] M` with the
residue-field fibre `ū_𝔪 : N/𝔪N → M/𝔪M` injective ⟹ the cokernel `M ⧸ u(N)` is flat over `R`. -/
theorem coker_of_flat_of_fibre_injective (u : N →ₗ[R] M)
    (hbar : Function.Injective
      (LinearMap.lTensor (R ⧸ IsLocalRing.maximalIdeal R) u)) :
    Module.Flat R (M ⧸ LinearMap.range u) :=
  coker_flat_of_fibre_injective_forall u (fibre_injective_of_maximal u hbar)

end Module.Flat

/-! ## Variants of the local flatness criterion for the cokernel

Two further source hypotheses under which the residue-field-fibre criterion still applies, needed by
the special-fibre-exactness form (Stacks 00MI):

* `..._free`: `N` is *free* over `R` of arbitrary rank (not necessarily finite);
* `..._sModule`: `N` is finite over a local `R`-algebra `S` (finite over `S`, not over `R`).

Both go through the same base-change-to-`R ⧸ I` reduction as `fibre_injective_of_maximal`; only the
residue-field injectivity core changes.  The shared reduction is extracted first. -/

namespace Module.Flat

open TensorProduct.AlgebraTensorModule in
/-- **Shared base-change identification.**  For a proper ideal `I` (so `R ⧸ I` is again local, via
`IsLocalHom (Ideal.Quotient.mk I)`), the residue-field fibre of the base change `u' = (R ⧸ I) ⊗ u`,
taken *over* `R ⧸ I`, is injective.  This is the two-`cancelBaseChange` naturality argument inside
`fibre_injective_of_maximal`, extracted verbatim; it uses only flatness of `M` — neither finiteness
nor freeness of `N` — so both variants below share it. -/
private theorem residueField_fibre_baseChange_injective
    {R N M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    {I : Ideal R} [IsLocalRing (R ⧸ I)] [IsLocalHom (Ideal.Quotient.mk I)]
    (u : N →ₗ[R] M)
    (hbar : Function.Injective (LinearMap.lTensor (IsLocalRing.ResidueField R) u)) :
    Function.Injective (LinearMap.lTensor (IsLocalRing.ResidueField (R ⧸ I))
        (LinearMap.baseChange (R ⧸ I) u)) := by
  -- `hbar` says `ū_𝔪 = baseChange (ResidueField R) u` is injective.
  have hbarBC : Function.Injective ⇑(LinearMap.baseChange (IsLocalRing.ResidueField R) u) := by
    rw [LinearMap.baseChange_eq_ltensor]; exact hbar
  -- Tensoring up to the field extension `ResidueField R → k'` keeps it injective (`k'` flat).
  have hBfield : Function.Injective ⇑(LinearMap.lTensor (IsLocalRing.ResidueField (R ⧸ I))
      (LinearMap.baseChange (IsLocalRing.ResidueField R) u)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hbarBC
  -- Naturality of `cancelBaseChange` along `R → ResidueField R → k'`.
  have eqB := lTensor_comp_cancelBaseChange R (IsLocalRing.ResidueField R)
    (IsLocalRing.ResidueField (R ⧸ I)) (M := IsLocalRing.ResidueField (R ⧸ I))
    (N := N) (Q := M) u
  have eqBf : ⇑(LinearMap.lTensor (IsLocalRing.ResidueField (R ⧸ I)) u)
        ∘ ⇑(cancelBaseChange R (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField (R ⧸ I))
              (IsLocalRing.ResidueField (R ⧸ I)) N)
      = ⇑(cancelBaseChange R (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField (R ⧸ I))
              (IsLocalRing.ResidueField (R ⧸ I)) M)
        ∘ ⇑(LinearMap.lTensor (IsLocalRing.ResidueField (R ⧸ I))
              (lTensor (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R) u)) := by
    simpa only [LinearMap.coe_comp, coe_lTensor, LinearEquiv.coe_coe]
      using congrArg DFunLike.coe eqB
  have hStepB : Function.Injective ⇑(LinearMap.lTensor (IsLocalRing.ResidueField (R ⧸ I)) u) :=
    injective_of_comm_sq' eqBf
      (cancelBaseChange R (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField (R ⧸ I))
        (IsLocalRing.ResidueField (R ⧸ I)) N).surjective
      (cancelBaseChange R (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField (R ⧸ I))
        (IsLocalRing.ResidueField (R ⧸ I)) M).injective hBfield
  -- Naturality of `cancelBaseChange` along `R → R ⧸ I → k'`.
  have eqA := lTensor_comp_cancelBaseChange R (R ⧸ I)
    (IsLocalRing.ResidueField (R ⧸ I)) (M := IsLocalRing.ResidueField (R ⧸ I))
    (N := N) (Q := M) u
  have eqAf : ⇑(LinearMap.lTensor (IsLocalRing.ResidueField (R ⧸ I)) u)
        ∘ ⇑(cancelBaseChange R (R ⧸ I) (IsLocalRing.ResidueField (R ⧸ I))
              (IsLocalRing.ResidueField (R ⧸ I)) N)
      = ⇑(cancelBaseChange R (R ⧸ I) (IsLocalRing.ResidueField (R ⧸ I))
              (IsLocalRing.ResidueField (R ⧸ I)) M)
        ∘ ⇑(LinearMap.lTensor (IsLocalRing.ResidueField (R ⧸ I))
              (lTensor (R ⧸ I) (R ⧸ I) u)) := by
    simpa only [LinearMap.coe_comp, coe_lTensor, LinearEquiv.coe_coe]
      using congrArg DFunLike.coe eqA
  exact injective_of_comm_sq eqAf
    (cancelBaseChange R (R ⧸ I) (IsLocalRing.ResidueField (R ⧸ I))
      (IsLocalRing.ResidueField (R ⧸ I)) N).injective hStepB

/-- **Residue-field core, `R`-free source.**  The analogue of
`injective_of_lTensor_residueField_injective` for `N` *free* over `R` (any rank — not necessarily
finite): a basis `b` of `N` provides a `ResidueField R`-basis `1 ⊗ b` of `ResidueField R ⊗ N`
directly (`Basis.baseChange`), so injectivity of the residue-field fibre makes `(mk_M ∘ u ∘ b)`
linearly independent, and `IsLocalRing.linearIndependent_of_flat` gives `LinearIndependent R (u ∘ b)`.
Since `b` spans `N`, no minimal-generator lift or `span_eq_top`/finiteness step is needed. -/
private theorem injective_of_lTensor_residueField_injective_free
    {R N M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup N] [Module R N] [Module.Free R N]
    [AddCommGroup M] [Module R M] [Module.Flat R M] (u : N →ₗ[R] M)
    (hbar : Function.Injective (LinearMap.lTensor (IsLocalRing.ResidueField R) u)) :
    Function.Injective u := by
  classical
  -- A basis `b` of `N` (from freeness); the family `v = u ∘ b` sits in `M`.
  let b := Module.Free.chooseBasis R N
  -- `hbar` says `k ⊗ u`, equivalently `baseChange k u`, is injective.
  have hbar' : Function.Injective ⇑(LinearMap.baseChange (IsLocalRing.ResidueField R) u) := by
    rw [LinearMap.baseChange_eq_ltensor]; exact hbar
  -- `k ⊗ (u ∘ b) = (baseChange k u) ∘ (b.baseChange k)` is `k`-linearly independent…
  have hli : LinearIndependent (IsLocalRing.ResidueField R)
      (TensorProduct.mk R (IsLocalRing.ResidueField R) M 1 ∘ (⇑u ∘ ⇑b)) := by
    have key : (TensorProduct.mk R (IsLocalRing.ResidueField R) M 1) ∘ (⇑u ∘ ⇑b)
        = ⇑(LinearMap.baseChange (IsLocalRing.ResidueField R) u)
            ∘ ⇑(b.baseChange (IsLocalRing.ResidueField R)) := by
      ext i; simp
    rw [key]
    exact (b.baseChange (IsLocalRing.ResidueField R)).linearIndependent.map' _
      (LinearMap.ker_eq_bot.mpr hbar')
  -- …so `u ∘ b` is `R`-linearly independent (flatness of `M`).
  have hui : LinearIndependent R (⇑u ∘ ⇑b) := IsLocalRing.linearIndependent_of_flat _ hli
  -- `b` spans `N`, so `Finsupp.linearCombination R b` is surjective.
  have hsurj : Function.Surjective (Finsupp.linearCombination R ⇑b) :=
    LinearMap.range_eq_top.mp (by rw [Finsupp.range_linearCombination, b.span_eq])
  -- `Finsupp.linearCombination R (u ∘ b) = u ∘ₗ Finsupp.linearCombination R b` is injective, and its
  -- second factor is surjective; therefore `u` is injective.
  have hui_inj : Function.Injective ⇑(u ∘ₗ Finsupp.linearCombination R ⇑b) := by
    rw [← Finsupp.linearCombination_linear_comp R u]; exact hui
  intro x y hxy
  obtain ⟨a, rfl⟩ := hsurj x
  obtain ⟨c, rfl⟩ := hsurj y
  exact congrArg (Finsupp.linearCombination R ⇑b) (hui_inj hxy)

/-- **Local criterion of flatness, `R`-free source.**  `ū_𝔪` injective ⟹ `ū_I` injective for every
finitely generated ideal `I`, with `N` free over `R`.  Copies the base-change reduction of
`fibre_injective_of_maximal` (via the shared `residueField_fibre_baseChange_injective`), calling the
free residue-field core over `R ⧸ I` — where `(R ⧸ I) ⊗ N` is `R ⧸ I`-free (`Module.Free.tensor`). -/
theorem fibre_injective_of_maximal_free
    {R N M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup N] [Module R N] [Module.Free R N]
    [AddCommGroup M] [Module R M] [Module.Flat R M] (u : N →ₗ[R] M)
    (hbar : Function.Injective (LinearMap.lTensor (R ⧸ IsLocalRing.maximalIdeal R) u)) :
    ∀ ⦃I : Ideal R⦄, I.FG → Function.Injective (LinearMap.lTensor (R ⧸ I) u) := by
  intro I _
  rcases eq_or_ne I ⊤ with rfl | hI_ne
  · -- `I = ⊤`: `(R ⧸ ⊤) ⊗ N` is a subsingleton.
    haveI : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    haveI : Subsingleton ((R ⧸ (⊤ : Ideal R)) ⊗[R] N) := Module.subsingleton (R ⧸ (⊤ : Ideal R)) _
    exact Function.injective_of_subsingleton _
  · -- `I ≠ ⊤`: base-change to the local ring `R ⧸ I` and apply the free core to `baseChange (R⧸I) u`.
    haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI_ne
    haveI : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    haveI : IsLocalHom (Ideal.Quotient.mk I) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have hbar'' := residueField_fibre_baseChange_injective (I := I) u hbar
    have hinj : Function.Injective ⇑(LinearMap.baseChange (R ⧸ I) u) :=
      injective_of_lTensor_residueField_injective_free _ hbar''
    rwa [LinearMap.baseChange_eq_ltensor] at hinj

/-- **Stacks 00ME variant — `R`-free source (arbitrary rank).**

`R` Noetherian local, `N` a *free* `R`-module (not necessarily finite), `M` a flat `R`-module,
`u : N →ₗ[R] M` with residue-field fibre `ū_𝔪 : N/𝔪N → M/𝔪M` injective ⟹ the cokernel `M ⧸ u(N)`
is flat over `R`.  Composition `coker_flat_of_fibre_injective_forall ∘ fibre_injective_of_maximal_free`. -/
theorem coker_of_flat_of_fibre_injective_free
    {R N M : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup N] [Module R N] [Module.Free R N]
    [AddCommGroup M] [Module R M] [Module.Flat R M] (u : N →ₗ[R] M)
    (hbar : Function.Injective (LinearMap.lTensor (R ⧸ IsLocalRing.maximalIdeal R) u)) :
    Module.Flat R (M ⧸ LinearMap.range u) :=
  coker_flat_of_fibre_injective_forall u (fibre_injective_of_maximal_free u hbar)

/-! ### The `𝔪`-adic descent step

The three private lemmas below are the machinery of
`injective_of_lTensor_residueField_injective_sModule`'s inductive step; see its docstring for the
mathematical route.  They are stated over fresh type variables (`A`, `P`, `Q`) so that none of the
section variables of this file is auto-bound into them. -/

section SModuleCore

variable {A : Type*} [CommRing A] {P Q : Type*}
  [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]

/-- The multiplication map `I ⊗[A] P → P`, `a ⊗ p ↦ a • p`, as `A`-linear. -/
private noncomputable def idealSMulMap (I : Ideal A) (P : Type*) [AddCommGroup P] [Module A P] :
    I ⊗[A] P →ₗ[A] P :=
  (TensorProduct.lid A P).toLinearMap ∘ₗ LinearMap.rTensor P I.subtype

@[simp]
private theorem idealSMulMap_tmul (I : Ideal A) (P : Type*) [AddCommGroup P] [Module A P]
    (a : I) (p : P) : idealSMulMap I P (a ⊗ₜ p) = (a : A) • p := rfl

/-- `idealSMulMap I P` is injective when `P` is flat: it is `rTensor P I.subtype` (injective by
flatness) followed by the unitor. -/
private theorem injective_idealSMulMap (I : Ideal A) (P : Type*) [AddCommGroup P] [Module A P]
    [Module.Flat A P] : Function.Injective (idealSMulMap I P) :=
  (TensorProduct.lid A P).injective.comp
    (Module.Flat.rTensor_preserves_injective_linearMap I.subtype Subtype.val_injective)

private theorem idealSMulMap_lTensor (I : Ideal A) (u : P →ₗ[A] Q) (t : I ⊗[A] P) :
    idealSMulMap I Q (LinearMap.lTensor I u t) = u (idealSMulMap I P t) := by
  induction t with
  | zero => simp
  | tmul a p => simp
  | add s t hs ht => simp [hs, ht]

private theorem mem_smul_of_idealSMulMap_lTensor_subtype (I : Ideal A) (W : Submodule A P)
    (s : I ⊗[A] W) : idealSMulMap I P (LinearMap.lTensor I W.subtype s) ∈ I • W := by
  induction s with
  | zero => simpa using Submodule.zero_mem _
  | tmul a y => exact Submodule.smul_mem_smul a.2 y.2
  | add s t hs ht => simpa using Submodule.add_mem _ hs ht

/-- **The inductive step of the local criterion, with no graded machinery.**

If `u` kills `x` and `x ∈ I • N`, then already `x ∈ (I * 𝔪) • N`.  The only use of flatness is the
injectivity of `I ⊗ M → M`; the only use of `hbar` is that an injective map of `k`-vector spaces
splits, so that `lTensor I` of it is injective too. -/
private theorem mem_mul_smul_top_of_mem_smul_top {R N M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M] [Module.Flat R M]
    (u : N →ₗ[R] M)
    (hbar : Function.Injective (LinearMap.lTensor (IsLocalRing.ResidueField R) u))
    (I : Ideal R) {x : N} (hx : x ∈ I • (⊤ : Submodule R N)) (hux : u x = 0) :
    x ∈ (I * IsLocalRing.maximalIdeal R) • (⊤ : Submodule R N) := by
  classical
  set k := IsLocalRing.ResidueField R with hk
  set 𝔪 := IsLocalRing.maximalIdeal R with hm
  set mkN : N →ₗ[R] k ⊗[R] N := (TensorProduct.mk R k N) 1 with hmkN
  set mkM : M →ₗ[R] k ⊗[R] M := (TensorProduct.mk R k M) 1 with hmkM
  -- 1. lift `x` through the multiplication map
  obtain ⟨t, ht⟩ : ∃ t : I ⊗[R] N, idealSMulMap I N t = x := by
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha n _
      exact ⟨⟨a, ha⟩ ⊗ₜ n, rfl⟩
    · rintro y z ⟨s, rfl⟩ ⟨w, rfl⟩
      exact ⟨s + w, by simp⟩
  -- 2. flatness of `M` turns `u x = 0` into the vanishing of the lift
  have h2 : LinearMap.lTensor (↥I) u t = 0 := by
    apply injective_idealSMulMap I M
    rw [idealSMulMap_lTensor, ht, hux, map_zero]
  -- 3. push into the residue-field fibre, by naturality of `p ↦ 1 ⊗ p`
  have hnat : (LinearMap.lTensor k u) ∘ₗ mkN = mkM ∘ₗ u := by ext n; simp [hmkN, hmkM]
  have h3 : LinearMap.lTensor (↥I) (LinearMap.lTensor k u)
      (LinearMap.lTensor (↥I) mkN t) = 0 := by
    have h := congrArg (LinearMap.lTensor (↥I)) hnat
    rw [LinearMap.lTensor_comp, LinearMap.lTensor_comp] at h
    have h' := LinearMap.congr_fun h t
    simp only [LinearMap.coe_comp, Function.comp_apply] at h'
    rw [h', h2, map_zero]
  -- 4. `lTensor k u` splits over the field `k`, so `lTensor I` of it is injective
  have hbar' : Function.Injective ⇑(LinearMap.baseChange k u) := by
    rw [LinearMap.baseChange_eq_ltensor]; exact hbar
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.baseChange k u)
    (LinearMap.ker_eq_bot.mpr hbar')
  have hcomp : (r.restrictScalars R) ∘ₗ (LinearMap.lTensor k u) = LinearMap.id := by
    refine LinearMap.ext fun y ↦ ?_
    have := LinearMap.congr_fun hr y
    simpa [LinearMap.baseChange_eq_ltensor] using this
  have hid : LinearMap.lTensor (↥I) (r.restrictScalars R) ∘ₗ
      LinearMap.lTensor (↥I) (LinearMap.lTensor k u) = LinearMap.id := by
    rw [← LinearMap.lTensor_comp, hcomp, LinearMap.lTensor_id]
  have h4 : LinearMap.lTensor (↥I) mkN t = 0 := by
    have := LinearMap.congr_fun hid (LinearMap.lTensor (↥I) mkN t)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at this
    rw [← this, h3, map_zero]
  -- 5. right-exactness: `t` comes from `I ⊗ 𝔪N`, whose multiplication image is `(I * 𝔪) • ⊤`
  have hker : LinearMap.ker mkN = 𝔪 • (⊤ : Submodule R N) := by
    have h := quotTensorEquivQuotSMul_comp_mk (M := N) 𝔪
    rw [← Submodule.ker_mkQ (𝔪 • (⊤ : Submodule R N)), ← h]
    ext y
    simp only [LinearMap.mem_ker, hmkN, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe]
    exact (map_eq_zero_iff _ (quotTensorEquivQuotSMul N 𝔪).injective).symm
  have hex : Function.Exact ⇑(𝔪 • (⊤ : Submodule R N)).subtype ⇑mkN := by
    rw [LinearMap.exact_iff, hker, Submodule.range_subtype]
  have hsurj : Function.Surjective ⇑mkN :=
    TensorProduct.mk_surjective R N k Ideal.Quotient.mk_surjective
  -- NB `_root_.` is load-bearing: inside `namespace Module.Flat` the bare name resolves to
  -- `Module.Flat.lTensor_exact`, which has a different signature.
  obtain ⟨s, hs⟩ := (_root_.lTensor_exact (↥I) hex hsurj t).mp h4
  rw [← ht, ← hs, ← Ideal.smul_eq_mul, Submodule.smul_assoc]
  exact mem_smul_of_idealSMulMap_lTensor_subtype I (𝔪 • ⊤) s

/-- Along a **local** homomorphism `R → S`, the `𝔪ᴿ`-adic filtration of `N` refines its `𝔪ˢ`-adic
filtration: `𝔪ᴿⁿ • ⊤ ≤ 𝔪ˢⁿ • ⊤` as sets.  This is what carries the descent step's conclusion into
the ring over which `N` is finite, so that Krull's intersection theorem applies. -/
private theorem smul_top_pow_le_restrictScalars (R S N : Type*) [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] (n : ℕ) {x : N}
    (hx : x ∈ (IsLocalRing.maximalIdeal R ^ n) • (⊤ : Submodule R N)) :
    x ∈ (IsLocalRing.maximalIdeal S ^ n) • (⊤ : Submodule S N) := by
  induction n generalizing x with
  | zero => simpa using Submodule.mem_top
  | succ n ih =>
      rw [pow_succ', ← Ideal.smul_eq_mul, Submodule.smul_assoc] at hx
      refine Submodule.smul_induction_on hx (fun a ha y hy ↦ ?_) (fun y z hy hz ↦ ?_)
      · have haS : algebraMap R S a ∈ IsLocalRing.maximalIdeal S := by
          rw [IsLocalRing.mem_maximalIdeal] at ha ⊢
          exact fun hu ↦ ha (isUnit_of_map_unit (algebraMap R S) a hu)
        rw [← algebraMap_smul S a y, pow_succ', ← Ideal.smul_eq_mul, Submodule.smul_assoc]
        exact Submodule.smul_mem_smul haS (ih hy)
      · exact Submodule.add_mem _ hy hz

end SModuleCore

/-- **Local criterion of flatness — the residue-field core, `S`-module source (Artin–Rees).**

Let `R → S` be a local homomorphism of local rings with `S` Noetherian, `N` a finite `S`-module (so
finite over `S`, *not* over `R`), `M` an `R`-flat module, and `u : N →ₗ[R] M` an `R`-linear map.  If
the residue-field fibre `ū_𝔪ᴿ = k_R ⊗ u` (over `R`) is injective, then `u` itself is injective.

This is the genuine Artin–Rees/Krull-intersection content of the local criterion of flatness
(Matsumura, *Commutative Ring Theory*, Theorem 22.3; Stacks tag 00MK), in the form where the source
`N` is finite only over the *upper* ring `S`.  Unlike `injective_of_lTensor_residueField_injective`
(finite over `R`) and `injective_of_lTensor_residueField_injective_free` (free over `R`) — which
reduce to `IsLocalRing.linearIndependent_of_flat` with no separation bootstrap — this case must run
the full descending-filtration argument:

* Let `K = ker u`.  One shows `K ⊆ 𝔪ᴿⁿ • N` for every `n`, by induction on `n`:
  * `n = 1`: injectivity of `ū_𝔪ᴿ` says exactly `K ⊆ 𝔪ᴿ • N` (if `u x = 0` then `x mod 𝔪ᴿN` is
    killed by `ū_𝔪ᴿ`, hence `x ∈ 𝔪ᴿ • N`).
  * `n → n+1`: `𝔪ᴿⁿ • N ∩ K ⊆ 𝔪ᴿⁿ⁺¹ • N` — see the route below.
* Since `algebraMap R S` is local, `𝔪ᴿ • N ⊆ 𝔪ˢ • N`, hence `𝔪ᴿⁿ • N ⊆ 𝔪ˢⁿ • N`, so
  `K ⊆ ⨅ₙ 𝔪ˢⁿ • N`.  By Krull's intersection theorem over the Noetherian local ring `S`
  (`Ideal.iInf_pow_smul_eq_bot_of_isLocalRing`, applied with the module `N` finite over `S`),
  `⨅ₙ 𝔪ˢⁿ • N = ⊥`, so `K = ⊥` and `u` is injective.

### The inductive step (route, 2026-08-09)

An earlier version of this docstring routed the inductive step through the Artin–Rees lemma
(`Ideal.exists_pow_inf_eq_pow_smul`).  **Artin–Rees is not needed** — the step is the usual
"associated graded" step of the local criterion, and it can be run with no graded machinery at all,
because `N ⧸ 𝔪ᴿN` is already a `k`-module and so `𝔪ᴿⁿ ⊗[R] (N ⧸ 𝔪ᴿN)` *is* the graded piece
`(𝔪ᴿⁿ ⧸ 𝔪ᴿⁿ⁺¹) ⊗[k] (N ⧸ 𝔪ᴿN)` on the nose.  Writing `I = 𝔪ᴿⁿ`, `μ_P : I ⊗[R] P → P` for
multiplication and `ρ_P : I ⊗[R] P → I ⊗[R] (P ⧸ 𝔪ᴿP)` for `lTensor I (mkQ _)`:

1. `x ∈ I • N` gives `t : I ⊗[R] N` with `μ_N t = x`.
2. `μ_M ((lTensor I u) t) = u (μ_N t) = u x = 0`, and `μ_M` is **injective because `M` is
   `R`-flat** (it is `rTensor M I.subtype` followed by `TensorProduct.lid`).  So
   `(lTensor I u) t = 0`.
3. Apply `ρ_M` and use naturality `ρ_M ∘ lTensor I u = lTensor I ū ∘ ρ_N`:
   `(lTensor I ū) (ρ_N t) = 0`.
4. `lTensor I ū` is injective: transport along
   `TensorProduct.AlgebraTensorModule.cancelBaseChange` to read `I ⊗[R] (P ⧸ 𝔪ᴿP)` as
   `(I ⊗[R] k) ⊗[k] (P ⧸ 𝔪ᴿP)`; over the field `k` every module is flat, and `ū` is injective by
   hypothesis.  Hence `ρ_N t = 0`.
5. `ker ρ_N` is the image of `I ⊗ 𝔪ᴿN` (right-exactness of `⊗`), whose image under `μ_N` lands in
   `𝔪ᴿⁿ⁺¹ • N`.  So `x = μ_N t ∈ 𝔪ᴿⁿ⁺¹ • N`.

Only step 2 uses flatness, and only through `Module.Flat.rTensor_preserves_injective_linearMap`
applied to `I.subtype`.  The `cancelBaseChange` idiom in step 4 is the same one
`fibre_injective_of_maximal` already uses twice.

Proved (2026-08-09) along exactly that route, in two pieces: the filtration descent is
`injective_of_lTensor_residueField_injective_of_separated`, which takes the separatedness of the
`𝔪ᴿ`-adic filtration as a bare hypothesis and mentions no `S` at all; this theorem supplies that
hypothesis from Krull over `S`.  Consumers that cannot conveniently produce the `S`-package (an
`Algebra`, an upper-ring module structure and an `S`-finiteness on the source) should use the
separated form directly. -/
theorem injective_of_lTensor_residueField_injective_of_separated
    {R N M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M] [Module.Flat R M] (u : N →ₗ[R] M)
    (hbar : Function.Injective (LinearMap.lTensor (IsLocalRing.ResidueField R) u))
    (hsep : ∀ x : N, (∀ n : ℕ, x ∈ (IsLocalRing.maximalIdeal R ^ n) • (⊤ : Submodule R N)) →
      x = 0) :
    Function.Injective u := by
  rw [injective_iff_map_eq_zero]
  intro x hux
  refine hsep x fun n ↦ ?_
  -- Descend `x` through the `𝔪ᴿ`-adic filtration, one power at a time.
  induction n with
  | zero => simpa using Submodule.mem_top
  | succ n ih =>
      rw [pow_succ]
      exact mem_mul_smul_top_of_mem_smul_top u hbar _ ih hux

theorem injective_of_lTensor_residueField_injective_sModule
    {R S N M : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] [Module.Finite S N]
    [AddCommGroup M] [Module R M] [Module.Flat R M] (u : N →ₗ[R] M)
    (hbar : Function.Injective (LinearMap.lTensor (IsLocalRing.ResidueField R) u)) :
    Function.Injective u := by
  refine injective_of_lTensor_residueField_injective_of_separated u hbar fun x hfil ↦ ?_
  -- Transfer the filtration to `S`, where `N` is finite and Krull applies.
  have hSfil : ∀ n : ℕ, x ∈ (IsLocalRing.maximalIdeal S ^ n) • (⊤ : Submodule S N) :=
    fun n ↦ smul_top_pow_le_restrictScalars R S N n (hfil n)
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := N) (IsLocalRing.maximalIdeal S)
    (IsLocalRing.maximalIdeal.isMaximal S).ne_top
  have : x ∈ (⊥ : Submodule S N) := by
    rw [← hbot]
    exact Submodule.mem_iInf _ |>.mpr hSfil
  simpa using this

/-- The `S`-module residue-field core `injective_of_lTensor_residueField_injective_sModule`
specialised to the base change along a proper ideal `I`: if the residue-field fibre of
`u' = (R ⧸ I) ⊗ u` over the local ring `R ⧸ I` is injective, then `u'` is injective.  This is that
core over `R ⧸ I` with upper ring `S ⧸ IS` — over which `(R ⧸ I) ⊗ N` is finite, via
`(R ⧸ I) ⊗_R N ≅ (S ⧸ IS) ⊗_S N` — so the `S ↦ S ⧸ IS` instance transport (descending the algebra,
module and finiteness structures) is the only bookkeeping beyond the core.

**Status (2026-08-09): this is the *only* `sorry` in the file, and the mathematics is done.**  The
core is proved and axiom-clean, and — deliberately — it was split so that this consumer never has
to build `S ⧸ IS`:  use `injective_of_lTensor_residueField_injective_of_separated`, which takes

  `hsep : ∀ x, (∀ n, x ∈ 𝔪ᴿⁿ • (⊤ : Submodule R N)) → x = 0`

in place of `[Algebra R S] [IsNoetherianRing S] [Module.Finite S N]`.  That hypothesis is *all* the
argument ever uses `S` for.

### The remaining obligation, in full

Apply the separated core with `R' := R ⧸ I`, `N' := (R ⧸ I) ⊗[R] N`, `M' := (R ⧸ I) ⊗[R] M`
(flat by base change of flatness) and `u' := LinearMap.baseChange (R ⧸ I) u`, with `hbar''` as the
fibre hypothesis.  Only `hsep` for `N'` is owed, and it reduces in four steps, none of which needs
a new algebra or module instance:

1. **`𝔪_{R⧸I} = (𝔪ᴿ).map (Ideal.Quotient.mk I)`.**  Not in mathlib for a general surjective local
   hom (`AdicCompletion.maximalIdeal_eq_map` is the only hit); prove it directly — `⊇` from
   `IsLocalHom`'s contrapositive (`¬IsUnit a → ¬IsUnit (f a)`), `⊆` from surjectivity plus the
   same.  About eight lines.
2. **`((𝔪ᴿ ^ n).map q) • (⊤ : Submodule (R ⧸ I) W) = Submodule.restrictScalars R ((𝔪ᴿ ^ n) • ⊤)`**
   for any `R ⧸ I`-module `W` — both inclusions by `Submodule.smul_le`, since the `R`-action on `W`
   factors through `q`.  So `hsep` over `R ⧸ I` is `hsep` over `R` for the same carrier.
3. **Transport along `quotTensorEquivQuotSMul N I : (R ⧸ I) ⊗[R] N ≃ₗ[R] N ⧸ I • ⊤`** (an `R`-linear
   equiv, so submodule membership moves across directly).
4. **Discharge `hsep` for `N ⧸ I • ⊤` from Krull over `S`.**  Lifting `y` to `z : N`, the
   hypothesis reads `∀ n, z ∈ 𝔪ᴿⁿ • ⊤ + I • ⊤`; `smul_top_pow_le_restrictScalars` upgrades the
   first summand to `𝔪ˢⁿ • ⊤`, and `I • (⊤ : Submodule R N) = (I.map (algebraMap R S)) • ⊤` as
   *sets* (both are the additive span of `{a • n : a ∈ I}`), so `z` lies in every
   `𝔪ˢⁿ • ⊤ + I' • ⊤`.  `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing` applied to the finite
   `S`-module `N ⧸ I' • ⊤` then gives `z ∈ I' • ⊤ = I • ⊤`, i.e. `y = 0`. -/
private theorem injective_baseChange_of_residueField_fibre_sModule
    {R S N M : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] [Module.Finite S N]
    [AddCommGroup M] [Module R M] [Module.Flat R M] (u : N →ₗ[R] M)
    {I : Ideal R} [IsLocalRing (R ⧸ I)] [IsLocalHom (Ideal.Quotient.mk I)]
    (hbar'' : Function.Injective (LinearMap.lTensor (IsLocalRing.ResidueField (R ⧸ I))
        (LinearMap.baseChange (R ⧸ I) u))) :
    Function.Injective ⇑(LinearMap.baseChange (R ⧸ I) u) := by
  sorry

/-- **Stacks 00ME variant — source finite over a local `R`-algebra `S`.**

`R` local, `R → S` a local homomorphism to a Noetherian local ring `S`, `N` a finite `S`-module,
`M` a flat `R`-module, `u : N →ₗ[R] M` with residue-field fibre `ū_𝔪ᴿ : N/𝔪ᴿN → M/𝔪ᴿM` injective
⟹ the cokernel `M ⧸ u(N)` is flat over `R`.  This is the form of the local criterion in which the
source module lives over the *upper* ring `S` (Stacks 00ME proper, cf. also Stacks 00MI).

Route: the pure-homological reduction `coker_flat_of_fibre_injective_forall` requires `ū_I` injective
for every finitely generated ideal `I` of `R`.  The `I = ⊤` fibre is a subsingleton.  For `I ≠ ⊤`,
base-change to the Noetherian local ring `R ⧸ I` (`residueField_fibre_baseChange_injective` gives the
residue-field fibre of `u' = (R ⧸ I) ⊗ u` injective) and apply the `S`-module residue-field core
`injective_of_lTensor_residueField_injective_sModule` over `R ⧸ I` — where the base change
`(R ⧸ I) ⊗ N` is finite over the Noetherian local ring `S ⧸ IS`.

The `I ≠ ⊤` step carries a single `sorry`, and as of 2026-08-09 it is **only** the
base-change-to-`R ⧸ I` instance plumbing `S ↦ S ⧸ IS`
(`injective_baseChange_of_residueField_fibre_sModule`, see its docstring for the exact package
still owed).  The residue-field core it feeds,
`injective_of_lTensor_residueField_injective_sModule`, is proved and axiom-clean; so are the
homological reduction and the `I = ⊤` case. -/
theorem coker_of_flat_of_fibre_injective_sModule
    {R S N M : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] [Module.Finite S N]
    [AddCommGroup M] [Module R M] [Module.Flat R M] (u : N →ₗ[R] M)
    (hbar : Function.Injective (LinearMap.lTensor (R ⧸ IsLocalRing.maximalIdeal R) u)) :
    Module.Flat R (M ⧸ LinearMap.range u) := by
  refine coker_flat_of_fibre_injective_forall u ?_
  intro I _
  rcases eq_or_ne I ⊤ with rfl | hI_ne
  · -- `I = ⊤`: `(R ⧸ ⊤) ⊗ N` is a subsingleton.
    haveI : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    haveI : Subsingleton ((R ⧸ (⊤ : Ideal R)) ⊗[R] N) := Module.subsingleton (R ⧸ (⊤ : Ideal R)) _
    exact Function.injective_of_subsingleton _
  · -- `I ≠ ⊤`: base-change to the local ring `R ⧸ I`; the residue-field fibre of `(R ⧸ I) ⊗ u` is
    -- injective (shared identification), and the `S`-module Artin–Rees core over `R ⧸ I`
    -- (with `(R ⧸ I) ⊗ N` finite over `S ⧸ IS`) then makes `(R ⧸ I) ⊗ u` injective.
    haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI_ne
    haveI : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    haveI : IsLocalHom (Ideal.Quotient.mk I) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have hbar'' := residueField_fibre_baseChange_injective (I := I) u hbar
    have hinj : Function.Injective ⇑(LinearMap.baseChange (R ⧸ I) u) :=
      -- `S` is not determined by `u` or `hbar''`; pass it explicitly (the `Module.Finite S N`
      -- instance search used to pin it and no longer does).
      injective_baseChange_of_residueField_fibre_sModule (S := S) u hbar''
    rwa [LinearMap.baseChange_eq_ltensor] at hinj

end Module.Flat
