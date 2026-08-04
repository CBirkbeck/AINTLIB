/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.GroupScheme.MuN

/-!
# The fibre square of constant schemes (route β, step 1's input)

`nonempty_weilPairing_of_root_of_trivialised` (`WeilPairing/DetCocycle.lean`) asks for a
trivialisation of `E[N] ×_S E[N]` by `constScheme S (A × A)`. A full level structure trivialises
`E[N]` itself (`fullLevelIso`, `GroupScheme/GLSchemeAction.lean`), so what is missing is the
identification of the *fibre square* of a constant scheme:

`constScheme S B ×_S constScheme S A ≅ constScheme S (B × A)`.

Two ingredients, neither of which needs the universality of coproducts:

* `isPullback_constSchemeMapAlong` (`GroupScheme/MuN.lean`) already says constant schemes are
  stable under base change, so the fibre square's apex is `constScheme (constScheme S A) B`;
* the double coproduct `∐_B ∐_A S` is `∐_{B × A} S` by a reindexing whose two directions are
  built from `Sigma.desc`/`Sigma.ι` and shown inverse by `Sigma.hom_ext` alone.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

variable (S : Scheme.{u}) (A B : Type) [Finite A] [Finite B]

/-- The reindexing of a double coproduct: `∐_{b : B} ∐_{a : A} S ≅ ∐_{(b, a)} S`.

Both directions are assembled from the coproduct inclusions, and both composites are identities
by coproduct extensionality — no universality of coproducts is involved. -/
noncomputable def constSchemeSigmaIso :
    constScheme (constScheme S A) B ≅ constScheme S (B × A) where
  hom := Sigma.desc fun b => Sigma.desc fun a => Sigma.ι (fun _ : B × A => S) (b, a)
  inv := Sigma.desc fun ba =>
    Sigma.ι (fun _ : A => S) ba.2 ≫ Sigma.ι (fun _ : B => constScheme S A) ba.1
  hom_inv_id := by
    refine Sigma.hom_ext _ _ fun b => Sigma.hom_ext _ _ fun a => ?_
    simp
  inv_hom_id := by
    refine Sigma.hom_ext _ _ fun ba => ?_
    simp

@[reassoc (attr := simp)]
theorem ι_constSchemeSigmaIso_hom (b : B) (a : A) :
    Sigma.ι (fun _ : A => S) a ≫ Sigma.ι (fun _ : B => constScheme S A) b ≫
        (constSchemeSigmaIso S A B).hom =
      Sigma.ι (fun _ : B × A => S) (b, a) := by
  simp [constSchemeSigmaIso]

/-- The reindexing is compatible with the structure morphisms: both read a point of `∐_B ∐_A S`
as its underlying point of `S`. -/
theorem constSchemeSigmaIso_hom_π :
    (constSchemeSigmaIso S A B).hom ≫ constSchemeπ S (B × A) =
      constSchemeπ (constScheme S A) B ≫ constSchemeπ S A := by
  refine Sigma.hom_ext _ _ fun b => Sigma.hom_ext _ _ fun a => ?_
  simp [constSchemeSigmaIso]

/-- **(route β, step 1's input)** The fibre square of constant schemes is the constant scheme on
the product index:

`constScheme S B ×_S constScheme S A ≅ constScheme S (B × A)`.

`isPullback_constSchemeMapAlong` identifies the apex as `constScheme (constScheme S A) B`;
`constSchemeSigmaIso` reindexes the double coproduct. -/
noncomputable def constSchemeSqIso :
    pullback (constSchemeπ S B) (constSchemeπ S A) ≅ constScheme S (B × A) :=
  (isPullback_constSchemeMapAlong (S := S) (constSchemeπ S A) B).isoPullback.symm.trans
    (constSchemeSigmaIso S A B)

/-- The computation rule for `constSchemeSqIso`: the `(b, a)`-th copy of `S` is the pair of the
`b`-th and `a`-th copies. Checked on the two pullback projections. -/
theorem constSchemeSqIso_inv_ι (b : B) (a : A) :
    Sigma.ι (fun _ : B × A => S) (b, a) ≫ (constSchemeSqIso S A B).inv =
      pullback.lift (Sigma.ι (fun _ : B => S) b) (Sigma.ι (fun _ : A => S) a)
        (by simp [constSchemeπ]) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, constSchemeSqIso, Iso.trans_inv, Iso.symm_inv, Category.assoc,
      IsPullback.isoPullback_hom_fst, pullback.lift_fst, constSchemeSigmaIso]
    simp only [Iso.symm_inv, Sigma.ι_desc_assoc, Sigma.ι_desc, Category.assoc]
    rw [ι_constSchemeMapAlong]
    simp [constSchemeπ]
  · rw [Category.assoc, constSchemeSqIso, Iso.trans_inv, Iso.symm_inv, Category.assoc,
      IsPullback.isoPullback_hom_snd, pullback.lift_snd, constSchemeSigmaIso]
    simp only [Iso.symm_inv, Sigma.ι_desc_assoc, Sigma.ι_desc, Category.assoc]
    simp [constSchemeπ]

/-- …and it is an isomorphism over `S`. -/
theorem constSchemeSqIso_hom_π :
    (constSchemeSqIso S A B).hom ≫ constSchemeπ S (B × A) =
      pullback.snd (constSchemeπ S B) (constSchemeπ S A) ≫ constSchemeπ S A := by
  rw [constSchemeSqIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    constSchemeSigmaIso_hom_π, Iso.inv_comp_eq,
    (isPullback_constSchemeMapAlong (S := S) (constSchemeπ S A) B).isoPullback_hom_snd_assoc]

end ModularCurves
