/-
================================================================================
PR DRAFT #4 — `IdealSheafData.exists_factor_comap_iff`  (staged locally)
================================================================================
Owner action: submitting to mathlib is an owner decision. Strip this block first.

* TARGET FILE : Mathlib/AlgebraicGeometry/IdealSheaf/Functorial.lean
* PLACEMENT   : after `comapIso` (~line 43) — this is the factoring dictionary the
                existing `comapIso` iso is the raw data for.
* CLASS       : fills-cited-gap. `comapIso` exists; the "factors-through" corollary
                (the shape consumers actually use) does not.
* PROOF       : 6 lines via `comapIso_hom_fst` / `comapIso_inv_subschemeι` + the
                pullback universal property — self-contained, no new imports beyond
                what Functorial.lean already has.
* NOTE        : can ship in the SAME PR as draft #3 (same target file) or separately.
* SOURCE      : ForMathlib/IdealSheafComapMul.lean:273 (verified compiling, axiom-clean).
================================================================================
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Factoring through a pulled-back subscheme

`exists_factor_comap_iff`: a map `g : T ⟶ X` factors through the scheme-theoretic
preimage `(I.comap f).subscheme` iff its composite `g ≫ f` factors through `I.subscheme`.
This is the "factors-through" corollary of `comapIso`.
-/

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- **Factoring through a pulled-back subscheme = factoring through the original after
composing** (the `comapIso` dictionary). A map `g : T ⟶ X` factors through the scheme-
theoretic preimage `(I.comap f).subscheme` iff its composite `g ≫ f` factors through
`I.subscheme`. -/
lemma exists_factor_comap_iff {X Y T : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y)
    (g : T ⟶ X) :
    (∃ h : T ⟶ (I.comap f).subscheme, h ≫ (I.comap f).subschemeι = g) ↔
      (∃ h : T ⟶ I.subscheme, h ≫ I.subschemeι = g ≫ f) := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨h ≫ (I.comapIso f).hom ≫ pullback.snd f I.subschemeι, ?_⟩
    simp only [Category.assoc]
    rw [← pullback.condition, comapIso_hom_fst_assoc]
  · rintro ⟨h, hh⟩
    refine ⟨pullback.lift g h hh.symm ≫ (I.comapIso f).inv, ?_⟩
    rw [Category.assoc, comapIso_inv_subschemeι, pullback.lift_fst]

end AlgebraicGeometry.Scheme.IdealSheafData
