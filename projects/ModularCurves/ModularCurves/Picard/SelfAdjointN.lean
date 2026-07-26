/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Picard.DivisorClass
import ModularCurves.EllipticCurve.Torsion

/-!
# Restricted self-adjointness of `[N]` on the relative Picard group (DS4 Gap A, `(★)`/`(★′)`)

**Skeleton only — `/develop --decompose` Step 2.5. Not yet proved.**

The decisive input for the Katz–Mazur / GME construction of the relative Weil pairing.
Writing `κ_T(Q) = [𝒪(Q − 0)]` for `sectionToPicRel` and `m_N = [N]` on the base-changed
curve:

* `(★)`  `m_N^* κ_T(Q) = κ_T([N] Q)`     — the reusable form;
* `(★′)` `[N] Q = 0  ⟹  m_N^* κ_T(Q) = 1` — all the *construction* needs.

This is the theorem-of-the-square / principal-polarization content of the slogan "`[N]` is
self-dual". It does **not** follow from the existing `Pic`, `picRel` or `RelEffCartierDiv`
APIs, and it is *not* the same as Abel's theorem: with `picRel = Ker(0^*)` as codomain,
"`sectionToPicRel` is an isomorphism" is **false** (over a field `Pic(k) = 0`, so
`Ker(0^*) = Pic(E)` carries every degree, while `κ` hits only degree zero). Abel is an
isomorphism onto a *degree-zero* subfunctor, and the construction does not need it.

## Closest existing material (field level — read before attacking this)

`projects/HasseWeil/HasseWeil/Pic0/`:
* `TheoremOfSquareDivisorForm.kappaDivisor_add_linEquiv` — `κ(A+B) ∼ κ(A) + κ(B)`, proved
  **unconditionally in any characteristic** (Abel in divisor form, Silverman III.3.5);
* `TheoremOfSquareDivisorForm.tos_divisor`, `tos_toClass` — the theorem of the square;
* `PicDualPullbackTheoremOfSquare.tos_pullback_principal_of_sigma_eq_zero` — the pullback
  form, with its residual pinned to a point identity.

Those are statements about Weierstrass divisors over a field; `(★′)` is the *relative,
sheafified* counterpart, so they give the shape of the argument rather than the argument.

## Note on the rigidification trap

`Pic` is built through `Skeleton`, so an equality of classes yields only a `Nonempty`
isomorphism, never a canonical one. The pairing construction downstream must therefore be
built on genuine **rigidified** invertible sheaves — the lift `L ↦ L ⊗ f^*(0^*L)⁻¹` of
`picRelProj`, carrying its canonical zero-section rigidification — and only descended to
Picard classes at the end. `(★′)` as stated here is the class-level shadow: it is what
supplies *existence* of the trivialization, after which
`EllipticCurveGeom.universallyOConnected` (`EllipticCurve/Rigidity.lean`, proved) makes the
normalized choice unique.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

variable {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}

/-- **(★)** `[N]^* κ_T(Q) = κ_T([N] Q)`: the reusable self-adjointness of `[N]` on the
relative Picard group. Stated in the raw section form `sectionToPicRel` itself uses. -/
theorem picMap_mulByHom_sectionToPicRel (N : ℕ) (t : T ⟶ S)
    (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π]
    (Q : T ⟶ pullback E.π t) (hQ : Q ≫ pullback.snd E.π t = 𝟙 T)
    (Q' : T ⟶ pullback E.π t) (hQ' : Q' ≫ pullback.snd E.π t = 𝟙 T)
    (hNQ : Q' = Q ≫ (E.baseChange t).mulByHom N) :
    Scheme.Pic.map ((E.baseChange t).mulByHom N)
        ((sectionToPicRel E.π E.zero E.zero_π hsm t Q hQ :
          Scheme.Pic (pullback E.π t))) =
      (sectionToPicRel E.π E.zero E.zero_π hsm t Q' hQ' :
        Scheme.Pic (pullback E.π t)) := by
  sorry

/-- **(★′)** The restricted form, which is all the Weil-pairing construction needs: the
pullback along `[N]` of the class of an `N`-torsion section is trivial. -/
theorem picMap_mulByHom_sectionToPicRel_eq_one (N : ℕ) (t : T ⟶ S)
    (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π]
    (Q : T ⟶ pullback E.π t) (hQ : Q ≫ pullback.snd E.π t = 𝟙 T)
    (hNQ : Q ≫ (E.baseChange t).mulByHom N = (E.baseChange t).zero) :
    Scheme.Pic.map ((E.baseChange t).mulByHom N)
        ((sectionToPicRel E.π E.zero E.zero_π hsm t Q hQ :
          Scheme.Pic (pullback E.π t))) = 1 := by
  sorry

end ModularCurves
