/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.CharZeroDescent

/-!
# Readings and `constSchemeMap` (route β, the last gap's public API)

The one remaining gap of route β is a statement about the *reading* of a map into a constant scheme
after postcomposition with `constSchemeMap`. `constIndex` — the reading's definition — is `private` in
`GroupScheme/MuN.lean`, so the statement has to be proved from the public face of the fibre
decomposition: `constSchemePointsEquiv_natural`, `constSchemePointsEquiv_sigmaι`,
`constMap_factor_of_le` and `mem_locConstPiece`.

`constSchemePointsEquiv_comp_constSchemeMap` below is that statement: postcomposing with
`constSchemeMap f` applies `f` to the reading. It is the tool that turns the scheme-level identity
`fullLevelHom_eq_of_levelCoord` into the pointwise comparison `hdet` needs.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

variable {S : Scheme.{u}} {A B : Type} [Finite A] [Finite B]

/-- Reading a `T`-point of `∐_A S` that factors through the `a`-component gives the constant `a`.

`constSchemePointsEquiv_natural` moves the reading of `g' ≫ Sigma.ι a` to a `comap` of the reading of
`Sigma.ι a`, which `constSchemePointsEquiv_sigmaι` evaluates. -/
theorem constSchemePointsEquiv_comp_sigmaι {T : Scheme.{u}} (g' : T ⟶ S) (a : A)
    {q : T ⟶ S} (hq : g' ≫ 𝟙 S = q)
    (hc : (g' ≫ Sigma.ι (fun _ : A => S) a) ≫ constSchemeπ S A = q) :
    constSchemePointsEquiv S A q ⟨g' ≫ Sigma.ι (fun _ : A => S) a, hc⟩ =
      LocallyConstant.const T a := by
  subst hq
  refine (constSchemePointsEquiv_natural S A (𝟙 S) g'
    ⟨Sigma.ι (fun _ : A => S) a, Sigma.ι_desc _ _⟩).trans ?_
  rw [constSchemePointsEquiv_sigmaι]
  ext t
  simp

/-- **(route β, the last gap's tool)** Postcomposing with `constSchemeMap f` applies `f` to the
reading.

Proved pointwise from the public fibre decomposition: at `t`, the reading `a` of `h` puts `t` in the
clopen piece where `h` factors through the `a`-component (`constMap_factor_of_le` at
`U := locConstPiece …`), so `h ≫ constSchemeMap f` factors through the `f a`-component there, and
`constSchemePointsEquiv_comp_sigmaι` reads that off as the constant `f a`. -/
theorem constSchemePointsEquiv_comp_constSchemeMap (f : A → B) {T : Scheme.{u}} (g : T ⟶ S)
    (h : { h : T ⟶ constScheme S A // h ≫ constSchemeπ S A = g }) :
    constSchemePointsEquiv S B g ⟨h.1 ≫ constSchemeMap (S := S) f, by
        rw [Category.assoc, constSchemeMap_π, h.2]⟩ =
      (constSchemePointsEquiv S A g h).map f := by
  ext t
  obtain ⟨a, ha⟩ : ∃ a : A, constSchemePointsEquiv S A g h t = a := ⟨_, rfl⟩
  set U := locConstPiece (constSchemePointsEquiv S A g h) a with hUdef
  have htU : t ∈ U := mem_locConstPiece.mpr ha
  have hfac : U.ι ≫ h.1 = (U.ι ≫ g) ≫ Sigma.ι (fun _ : A => S) a :=
    constMap_factor_of_le h.1 h.2 a (le_refl _)
  have hfac' : U.ι ≫ h.1 ≫ constSchemeMap (S := S) f =
      (U.ι ≫ g) ≫ Sigma.ι (fun _ : B => S) (f a) := by
    rw [← Category.assoc, hfac, Category.assoc, constSchemeMap_ι]
  have hread := constSchemePointsEquiv_natural S B g U.ι
    ⟨h.1 ≫ constSchemeMap (S := S) f, by rw [Category.assoc, constSchemeMap_π, h.2]⟩
  have hconst : constSchemePointsEquiv S B (U.ι ≫ g)
      ⟨U.ι ≫ h.1 ≫ constSchemeMap (S := S) f, by
        rw [Category.assoc, Category.assoc, constSchemeMap_π, h.2]⟩ =
      LocallyConstant.const U (f a) :=
    (congrArg (constSchemePointsEquiv S B (U.ι ≫ g))
        (Subtype.ext hfac' :
          (⟨U.ι ≫ h.1 ≫ constSchemeMap (S := S) f, by
              rw [Category.assoc, Category.assoc, constSchemeMap_π, h.2]⟩ :
            { m : U.toScheme ⟶ constScheme S B // m ≫ constSchemeπ S B = U.ι ≫ g }) =
          ⟨(U.ι ≫ g) ≫ Sigma.ι (fun _ : B => S) (f a), by
            rw [Category.assoc, Sigma.ι_desc, Category.comp_id]⟩)).trans
      (constSchemePointsEquiv_comp_sigmaι (U.ι ≫ g) (f a) (Category.comp_id _) _)
  have hval := congrArg (fun c => LocallyConstant.toFun c ⟨t, htU⟩) (hread.symm.trans hconst)
  rw [LocallyConstant.map_apply]
  simp only [Function.comp_apply, ha]
  exact hval

end ModularCurves
