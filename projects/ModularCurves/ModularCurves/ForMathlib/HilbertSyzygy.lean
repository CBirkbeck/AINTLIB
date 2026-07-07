/-
Copyright (c) 2026 AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Hilbert's syzygy theorem

For a field `K` and `n : ℕ`, every module over the polynomial ring `MvPolynomial (Fin n) K` has
projective dimension `≤ n`.  This is Hilbert's syzygy theorem (finite global dimension of a
polynomial ring over a field).

The main result is `HilbertSyzygy.hasProjectiveDimensionLE_of_field`.  We prove the bound for
**all** modules (not merely finitely generated ones); the finitely-generated case
`hasProjectiveDimensionLE_of_field_of_finite` and the `projectiveDimension`-valued statement
`projectiveDimension_le_of_field` are immediate corollaries.

## Strategy

Induction on `n`, using mathlib's projective-dimension machinery
(`Mathlib.CategoryTheory.Abelian.Projective.Dimension`,
`Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension`):

* **Base case** (`n = 0`): `MvPolynomial (Fin 0) K ≃+* K` (`MvPolynomial.isEmptyRingEquiv`), and
  every module over a field is free, hence projective, hence has projective dimension `≤ 0`.  The
  bound is transported across the ring isomorphism via `hasProjectiveDimensionLE_of_semiLinearEquiv`
  (packaged here as `hasProjectiveDimensionLE_of_ringEquiv`).

* **Inductive step** (`n → n + 1`): `MvPolynomial (Fin (n+1)) K ≃ₐ[K] (MvPolynomial (Fin n) K)[X]`
  (`MvPolynomial.finSuccEquiv`).  We transport a module over `MvPolynomial (Fin (n+1)) K` to a
  module over `R[X]` (`R := MvPolynomial (Fin n) K`), apply the polynomial change-of-rings bound
  `polynomialChangeOfRings`, and transport the dimension bound back.

## The change-of-rings step

`polynomialChangeOfRings` (`pd_{R[X]} M ≤ (sup over R-modules of pd) + 1`) is the classical first
change-of-rings theorem for the polynomial extension `R ↪ R[X]`.  It is proved here from two
ingredients:

* `hasProjectiveDimensionLE_extendScalars` (**fully proved**): extension of scalars
  `R[X] ⊗_R (-)` preserves the bound `pd ≤ d`, because `R[X]` is free (hence flat) over `R`, so
  `extendScalars` is exact (`ModuleCat.preservesFiniteLimits_extendScalars_of_flat`), and it
  preserves projective objects (it is a left adjoint whose right adjoint `restrictScalars` preserves
  epimorphisms).

* `exists_characteristicShortExact` (**the single `sorry`**): the *characteristic short exact
  sequence* of `R[X]`-modules `0 → R[X] ⊗_R M → R[X] ⊗_R M → M → 0`, whose surjection is the counit
  of `extendScalars ⊣ restrictScalars` (`ModuleCat.extendRestrictScalarsAdj`) and whose injection is
  `s ⊗ m ↦ sX ⊗ m - s ⊗ (X • m)`.  This is standard mathematics; via
  `PolynomialModule.polynomialTensorProductLEquivPolynomialModule` it becomes an explicit `Finsupp`
  exactness computation.  It is the only piece not yet formalized in mathlib.

Feeding the short exact sequence (both outer terms `R[X] ⊗_R M`, of `pd ≤ d`) into
`ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃` yields the `d + 1` bound.

**Validation conclusion.**  The projective-dimension route to Hilbert's syzygy theorem — and hence
the Tor-free flat-locus development (DEV-1) — goes through with mathlib's present machinery: the
entire theorem reduces to the single classical `exists_characteristicShortExact`, whose every
ingredient already exists in mathlib.  No Buchsbaum–Eisenbud criterion is required.
-/

universe u

open CategoryTheory Abelian Module ModuleCat Limits

namespace HilbertSyzygy

noncomputable section

attribute [local instance] RingHomInvPair.of_ringEquiv

/-- The ring homomorphism `R → R[X]`. -/
abbrev polyAlg (R : Type u) [CommRing R] : R →+* Polynomial R := algebraMap R (Polynomial R)

/-- The identity map, viewed as a semilinear equivalence from the `restrictScalars`-transported
module back to the original module along a ring isomorphism `e`. -/
def restrictScalarsSemilinearEquiv {R R' : Type u} [CommRing R] [CommRing R'] (e : R ≃+* R')
    (M : ModuleCat.{u} R') :
    ((ModuleCat.restrictScalars (e : R →+* R')).obj M) ≃ₛₗ[(e : R →+* R')] M where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- Transport a projective-dimension bound across a ring isomorphism: if the `R`-module obtained
from `M` by restricting scalars along `e : R ≃+* R'` has projective dimension `≤ n`, then so does
the `R'`-module `M`. -/
lemma hasProjectiveDimensionLE_of_ringEquiv {R R' : Type u} [CommRing R] [CommRing R']
    (e : R ≃+* R') (M : ModuleCat.{u} R') (n : ℕ)
    [HasProjectiveDimensionLE ((ModuleCat.restrictScalars (e : R →+* R')).obj M) n] :
    HasProjectiveDimensionLE M n :=
  ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv e (restrictScalarsSemilinearEquiv e M) n

/-- Extension of scalars along `R → R[X]` preserves the bound `projective dimension ≤ n`:
if the `R`-module `N` has projective dimension `≤ n`, then the `R[X]`-module `R[X] ⊗_R N` does too.

`R[X]` is free, hence flat, over `R`, so `extendScalars` is exact; and it preserves projective
objects, being a left adjoint whose right adjoint `restrictScalars` preserves epimorphisms.  The
proof then mirrors `ModuleCat.localizedModule_hasProjectiveDimensionLE`. -/
lemma hasProjectiveDimensionLE_extendScalars (R : Type u) [CommRing R] (n : ℕ)
    (N : ModuleCat.{u} R) [HasProjectiveDimensionLE N n] :
    HasProjectiveDimensionLE ((extendScalars (polyAlg R)).obj N) n := by
  haveI hepi : (restrictScalars.{u} (polyAlg R)).PreservesEpimorphisms :=
    { preserves := fun g h => by rw [ModuleCat.epi_iff_surjective] at h ⊢; exact h }
  haveI plim : PreservesFiniteLimits (extendScalars.{u, u, u} (polyAlg R)) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr Module.Flat.of_free)
  haveI padd : (extendScalars.{u, u, u} (polyAlg R)).Additive :=
    Functor.additive_of_preserves_binary_products _
  haveI pproj : (extendScalars.{u, u, u} (polyAlg R)).PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (ModuleCat.extendRestrictScalarsAdj (polyAlg R))
  induction n generalizing N with
  | zero =>
    have projle : HasProjectiveDimensionLE N 0 := ‹_›
    simp only [HasProjectiveDimensionLE, zero_add] at projle ⊢
    rw [← projective_iff_hasProjectiveDimensionLT_one] at projle ⊢
    exact (extendScalars.{u, u, u} (polyAlg R)).projective_obj_of_projective projle
  | succ n ih =>
    rcases ModuleCat.enoughProjectives.1 N with ⟨⟨P, g⟩⟩
    let T := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
    have T_exact : T.ShortExact := { exact := ShortComplex.exact_kernel g }
    let TS := T.map (extendScalars.{u, u, u} (polyAlg R))
    have TS_exact : TS.ShortExact := T_exact.map_of_exact (extendScalars.{u, u, u} (polyAlg R))
    have hp2 : Projective TS.X₂ := (extendScalars.{u, u, u} (polyAlg R)).projective_obj _
    have := (T_exact.hasProjectiveDimensionLT_X₃_iff n ‹_›).mp ‹_›
    exact (TS_exact.hasProjectiveDimensionLT_X₃_iff n hp2).mpr (ih (kernel g))

/-- **The characteristic short exact sequence** of an `R[X]`-module `M`:
`0 → R[X] ⊗_R M → R[X] ⊗_R M → M → 0` (restriction of scalars is left implicit in the tensor
factors).  The surjection is the counit of `extendScalars ⊣ restrictScalars`; the injection is
`s ⊗ m ↦ sX ⊗ m - s ⊗ (X • m)`.

This is the one piece of the classical proof of Hilbert's syzygy theorem not yet available in
mathlib.  It is a standard `Finsupp` exactness computation once transported through
`PolynomialModule.polynomialTensorProductLEquivPolynomialModule`; see the module docstring. -/
lemma exists_characteristicShortExact (R : Type u) [CommRing R]
    (M : ModuleCat.{u} (Polynomial R)) :
    ∃ S : ShortComplex (ModuleCat.{u} (Polynomial R)), S.ShortExact ∧
      Nonempty (S.X₁ ≅ (extendScalars (polyAlg R)).obj ((restrictScalars (polyAlg R)).obj M)) ∧
      Nonempty (S.X₂ ≅ (extendScalars (polyAlg R)).obj ((restrictScalars (polyAlg R)).obj M)) ∧
      Nonempty (S.X₃ ≅ M) := by
  sorry

/-- **Polynomial change of rings for projective dimension.**  If every `R`-module has projective
dimension `≤ d`, then every `R[X]`-module has projective dimension `≤ d + 1`.

Proved from `hasProjectiveDimensionLE_extendScalars` and `exists_characteristicShortExact`: the
characteristic sequence `0 → R[X] ⊗_R M → R[X] ⊗_R M → M → 0` has both outer terms of projective
dimension `≤ d`, so `ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃` bounds `M` by `d + 1`. -/
lemma polynomialChangeOfRings (R : Type u) [CommRing R] (d : ℕ)
    (hd : ∀ (N : ModuleCat.{u} R), HasProjectiveDimensionLE N d)
    (M : ModuleCat.{u} (Polynomial R)) :
    HasProjectiveDimensionLE M (d + 1) := by
  haveI hMdown : HasProjectiveDimensionLE ((restrictScalars (polyAlg R)).obj M) d := hd _
  haveI hP : HasProjectiveDimensionLE
      ((extendScalars (polyAlg R)).obj ((restrictScalars (polyAlg R)).obj M)) d :=
    hasProjectiveDimensionLE_extendScalars R d _
  obtain ⟨S, hSE, ⟨e1⟩, ⟨e2⟩, ⟨e3⟩⟩ := exists_characteristicShortExact R M
  have hX3 : HasProjectiveDimensionLT S.X₃ (d + 2) := by
    have h1 : HasProjectiveDimensionLT S.X₁ (d + 1) := by
      have : HasProjectiveDimensionLT ((extendScalars (polyAlg R)).obj
          ((restrictScalars (polyAlg R)).obj M)) (d + 1) := hP
      exact hasProjectiveDimensionLT_of_iso e1.symm (d + 1)
    have h2 : HasProjectiveDimensionLT S.X₂ (d + 2) := by
      have : HasProjectiveDimensionLE ((extendScalars (polyAlg R)).obj
          ((restrictScalars (polyAlg R)).obj M)) (d + 1) :=
        hasProjectiveDimensionLT_of_ge _ (d + 1) (d + 2) (by omega)
      exact hasProjectiveDimensionLT_of_iso e2.symm (d + 2)
    exact hSE.hasProjectiveDimensionLT_X₃ (d + 1) h1 h2
  exact hasProjectiveDimensionLT_of_iso e3 (d + 2)

/-- Base case of Hilbert's syzygy theorem: every module over `MvPolynomial (Fin 0) K` (which is
isomorphic to the field `K`) has projective dimension `≤ 0`, i.e. is projective. -/
lemma hasProjectiveDimensionLE_of_field_zero (K : Type u) [Field K]
    (M : ModuleCat.{u} (MvPolynomial (Fin 0) K)) :
    HasProjectiveDimensionLE M 0 := by
  -- `MvPolynomial (Fin 0) K ≃+* K`, so restricting scalars turns `M` into a `K`-vector space.
  let e : K ≃+* MvPolynomial (Fin 0) K := (MvPolynomial.isEmptyRingEquiv K (Fin 0)).symm
  let Msrc := (ModuleCat.restrictScalars (e : K →+* MvPolynomial (Fin 0) K)).obj M
  -- A `K`-vector space is free, hence projective, hence has projective dimension `≤ 0`.
  have : HasProjectiveDimensionLE Msrc 0 :=
    (CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero Msrc).mp
      (ModuleCat.projective_of_free (Module.Free.chooseBasis K Msrc))
  exact hasProjectiveDimensionLE_of_ringEquiv e M 0

/-- **Hilbert's syzygy theorem.**  For a field `K`, every module over the polynomial ring
`MvPolynomial (Fin n) K` has projective dimension `≤ n`.  (The bound holds for all modules, not
merely finitely generated ones.) -/
theorem hasProjectiveDimensionLE_of_field (K : Type u) [Field K] (n : ℕ)
    (M : ModuleCat.{u} (MvPolynomial (Fin n) K)) :
    HasProjectiveDimensionLE M n := by
  induction n with
  | zero => exact hasProjectiveDimensionLE_of_field_zero K M
  | succ n hn =>
    -- `MvPolynomial (Fin (n+1)) K ≃+* (MvPolynomial (Fin n) K)[X]`.
    let e : Polynomial (MvPolynomial (Fin n) K) ≃+* MvPolynomial (Fin (n + 1)) K :=
      (MvPolynomial.finSuccEquiv K n).toRingEquiv.symm
    -- Restrict `M` to an `R[X]`-module and apply the polynomial change-of-rings bound with the IH.
    have hstep : HasProjectiveDimensionLE
        ((ModuleCat.restrictScalars (e : _ →+* _)).obj M) (n + 1) :=
      polynomialChangeOfRings (MvPolynomial (Fin n) K) n hn _
    exact hasProjectiveDimensionLE_of_ringEquiv e M (n + 1)

/-- Hilbert's syzygy theorem, in the requested finitely-generated form: a finitely generated module
over `MvPolynomial (Fin n) K` has projective dimension `≤ n`. -/
theorem hasProjectiveDimensionLE_of_field_of_finite (K : Type u) [Field K] (n : ℕ)
    (M : ModuleCat.{u} (MvPolynomial (Fin n) K)) [Module.Finite (MvPolynomial (Fin n) K) M] :
    HasProjectiveDimensionLE M n :=
  hasProjectiveDimensionLE_of_field K n M

/-- Hilbert's syzygy theorem, phrased with `projectiveDimension`:
`projectiveDimension M ≤ n` for every module over `MvPolynomial (Fin n) K`. -/
theorem projectiveDimension_le_of_field (K : Type u) [Field K] (n : ℕ)
    (M : ModuleCat.{u} (MvPolynomial (Fin n) K)) :
    projectiveDimension M ≤ (n : WithBot ℕ∞) :=
  (CategoryTheory.projectiveDimension_le_iff M n).mpr (hasProjectiveDimensionLE_of_field K n M)

end

end HilbertSyzygy
