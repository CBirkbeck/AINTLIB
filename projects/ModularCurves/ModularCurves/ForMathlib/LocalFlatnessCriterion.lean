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
private theorem injective_of_lTensor_residueField_injective (u : N →ₗ[R] M)
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
  * `n → n+1`: the step uses `R`-flatness of `M` together with the Artin–Rees lemma
    (`Ideal.exists_pow_inf_eq_pow_smul`), giving `𝔪ᴿⁿ • N ∩ K ⊆ 𝔪ᴿⁿ⁺¹ • N`.
* Since `algebraMap R S` is local, `𝔪ᴿ • N ⊆ 𝔪ˢ • N`, hence `𝔪ᴿⁿ • N ⊆ 𝔪ˢⁿ • N`, so
  `K ⊆ ⨅ₙ 𝔪ˢⁿ • N`.  By Krull's intersection theorem over the Noetherian local ring `S`
  (`Ideal.iInf_pow_smul_eq_bot_of_isLocalRing`, applied with the module `N` finite over `S`),
  `⨅ₙ 𝔪ˢⁿ • N = ⊥`, so `K = ⊥` and `u` is injective.

Deferred (a single `sorry` for the whole argument): the inductive step is the only piece not already
packaged in mathlib; the surrounding Krull/Artin–Rees API (`Ideal.iInf_pow_smul_eq_bot_of_isLocalRing`,
`Ideal.exists_pow_inf_eq_pow_smul`) is in place. -/
theorem injective_of_lTensor_residueField_injective_sModule
    {R S N M : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] [Module.Finite S N]
    [AddCommGroup M] [Module R M] [Module.Flat R M] (u : N →ₗ[R] M)
    (hbar : Function.Injective (LinearMap.lTensor (IsLocalRing.ResidueField R) u)) :
    Function.Injective u := by
  -- The full descending-filtration (Artin–Rees / Krull) argument; see the docstring.
  sorry

/-- The `S`-module residue-field core `injective_of_lTensor_residueField_injective_sModule`
specialised to the base change along a proper ideal `I`: if the residue-field fibre of
`u' = (R ⧸ I) ⊗ u` over the local ring `R ⧸ I` is injective, then `u'` is injective.  This is that
core over `R ⧸ I` with upper ring `S ⧸ IS` — over which `(R ⧸ I) ⊗ N` is finite, via
`(R ⧸ I) ⊗_R N ≅ (S ⧸ IS) ⊗_S N` — so the `S ↦ S ⧸ IS` instance transport (descending the algebra,
module and finiteness structures) is the only bookkeeping beyond the core.  Deferred with a `sorry`. -/
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

The `I ≠ ⊤` step carries a single `sorry` (the Artin–Rees core plus its base-change-to-`R ⧸ I`
instance plumbing `S ↦ S ⧸ IS`); the homological reduction and the `I = ⊤` case are complete. -/
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
