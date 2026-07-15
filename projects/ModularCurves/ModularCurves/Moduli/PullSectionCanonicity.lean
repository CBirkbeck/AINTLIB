/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.Moduli.PullSectionAdd
import ModularCurves.EllipticCurve.RigiditySpreadingOut
import ModularCurves.EllipticCurve.RecordGroupUnique

/-!
# The T-E4 transport, reduced to the single canonicity primitive (Y1-D2)

`Moduli.PullSectionAdd` proves section-pullback additivity (`transportSection_add`,
`pullSection_add_of_isLocallyNoetherian`) over **locally noetherian** bases only, because it
invokes `isMonHom_of_one_comp_eq'` (GIT Cor 6.4, T-W7.7) — which currently carries
`[IsLocallyNoetherian S]`. The whole T-E4 family (unrestricted `pullSection_add`, the
`Γ₁`/`Γ(N)` naive functor-law memberships, and the Y₁(N) transport `Y1-D2`) inherits that
noetherian restriction — but **only through that one call**.

This file isolates the dependency. Reading `transportSection_add`'s proof, the base's
noetherianness is used **exclusively** to produce the group-homomorphism equation `h64` for
the comparison isomorphism `curveIsoPullbackOver`; everything downstream is noetherian-free
group algebra. So:

* `transportSection_add_of_isMonHom` (proved in `Moduli/PullSectionAdd.lean`, next to the
  noetherian specialisation that consumes it) takes that group-hom equation as a
  **hypothesis** and proves transport additivity **sorry-free, over an arbitrary base**.
  This is the single "one transport proof" that closes the whole family; this file supplies
  the hypothesis from the finite-presentation route.

The hypothesis is supplied three ways, all feeding the *same* lemma:
* `isMonHom_of_one_comp_eq'` (`Rigidity.lean`, noetherian) — recovers the existing
  `pullSection_add_of_isLocallyNoetherian`;
* `isMonHom_of_one_comp_eq'_of_finitePresentation` (`RigiditySpreadingOut.lean`, **route (a)**,
  T-W7.8) — gives the arbitrary-base result the moment route (a) lands;
* the explicit base-change-natural group law (**route (c)**, c5β's endgame `mulModelHom` →
  `T-W7a`) — same, the moment the endgame lands.

So the entire T-E4 family is now **collapsed to the single primitive
`isMonHom_of_one_comp_eq'_of_finitePresentation`** (arbitrary-base GIT Cor 6.4), which lands
via route (a) or route (c).

## Holder wiring note (T-E4-family, [Y1-D2])

The standalone lemmas here (all over an **arbitrary** base) let the holders close their
parked/`sorry`'d transport gates. Every one bottoms out at the *single* primitive
`isMonHom_of_one_comp_eq'_of_finitePresentation`, so all go axiom-clean the moment route (a)
(this repo's `RigiditySpreadingOut.lean`) *or* route (c) (c5β's endgame `T-W7a`) lands.

* **`Moduli/Representability.lean` holder** — `EllHom.pullSection_add` (the parked `:= by sorry`,
  ~L207): replace with `EllHom.pullSection_add_of_finitePresentation R f P Q`. The two functor-law
  memberships `gammaOneNaiveProblem.map` / `gammaFullNaiveProblem.map` (~L214/L229) then close: the
  `(N : ℤ) • P = 0` killing clause transports by `pullSection_add_of_finitePresentation` +
  `pullSection_zsmul_of_finitePresentation`; the fibrewise `Point.pull` clauses transport barehanded
  (pull commutes with `pullSection`, no group data). `pullSection_zsmul` (GammaHRepresentability,
  and hence `pullAlong_glSmul`/GH) can drop its `pullSection_add` hypothesis onto the FP version.
* **`ModularCurve/YOneAssembly.lean` ([Y1-D2], NEW-Y1)** — `isNaiveGammaOne_pullSection_iff` closes
  the same way: the killing clause via the two FP `pullSection` lemmas above; the fibrewise clauses
  (`(N:ℤ) • Point.pull … = 0`, exact-order-`N`) barehanded via pull/`pullSection` compatibility. Do
  **not** shared-edit — this note is the coordination; assemble in your own file/PR.
* **Coordination (attack-1, no duplication):** the canonicity transport is proved *once* — here, in
  `transportSection_add_of_isMonHom` (sorry-free) — and everything above consumes it. Do not
  re-derive the group-iso transport in the holder files.

## References

* Loeffler, §3.3/§3.7/§3.8 (the `Ell/R`-presheaf functor laws).
* Katz–Mazur, 2.1.2 / 3.2 (canonicity of the group law; naive level structures).
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  MonObj

universe u

namespace ModularCurves

namespace EllHom

variable (R : CommRingCat.{u}) {X Y : EllObj R} (f : X ⟶ Y)

/-- **(T-E4a over an arbitrary base — modulo the single route (a)/(c) canonicity primitive)**
Transport additivity, with the group-hom equation supplied by the arbitrary-base GIT Cor 6.4
`isMonHom_of_one_comp_eq'_of_finitePresentation` (route (a), `RigiditySpreadingOut.lean`).
Elliptic curves are smooth of relative dimension one, hence of finite presentation, so the
finite-presentation hypotheses are automatic. -/
theorem transportSection_add_of_finitePresentation (s s' : X.curve.Section) :
    transportSection R f (s + s')
      = transportSection R f s + transportSection R f s' := by
  haveI : Smooth X.curve.π := SmoothOfRelativeDimension.smooth (n := 1) (f := X.curve.π)
  haveI : Smooth (Y.curve.baseChange f.baseHom).π :=
    SmoothOfRelativeDimension.smooth (n := 1) (f := (Y.curve.baseChange f.baseHom).π)
  haveI : IsProper X.curve.asOver.hom := inferInstanceAs (IsProper X.curve.π)
  haveI : Flat X.curve.asOver.hom := inferInstanceAs (Flat X.curve.π)
  haveI : LocallyOfFinitePresentation X.curve.asOver.hom :=
    inferInstanceAs (LocallyOfFinitePresentation X.curve.π)
  haveI : IsSeparated (Y.curve.baseChange f.baseHom).asOver.hom :=
    inferInstanceAs (IsSeparated (Y.curve.baseChange f.baseHom).π)
  haveI : LocallyOfFinitePresentation (Y.curve.baseChange f.baseHom).asOver.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (Y.curve.baseChange f.baseHom).π)
  have hmon := isMonHom_of_pointedIso_records X.curve (Y.curve.baseChange f.baseHom)
    (Over.isoMk (curveIsoPullback R f) (f.isPullback.isoPullback_hom_snd))
    (curveIsoPullbackOver_one R f)
  exact transportSection_add_of_isMonHom R f hmon s s'

/-- **(T-E4a, `pullSection_add` over an arbitrary base)** Section-pullback is additive over an
arbitrary base — the unrestricted statement, modulo the single route (a)/(c) canonicity
primitive. Same proof as `pullSection_add_of_isLocallyNoetherian` but routed through
`transportSection_add_of_finitePresentation`, so the only remaining dependency is the
arbitrary-base GIT Cor 6.4 (not `[IsLocallyNoetherian]`). -/
theorem pullSection_add_of_finitePresentation (P Q : Y.curve.Section) :
    pullSection R f (P + Q)
      = pullSection R f P + pullSection R f Q := by
  apply transportSection_injective R f
  rw [transportSection_add_of_finitePresentation]
  apply (EllipticCurve.Point.baseChangeEquiv Y.curve f.baseHom (𝟙 X.base)).injective
  rw [map_add, dict_transportSection_pullSection, dict_transportSection_pullSection,
    dict_transportSection_pullSection, EllipticCurve.Point.pull_add]

/-- **(T-E4a, `pullSection_zsmul` over an arbitrary base)** `ℤ`-linearity of section-pullback
over an arbitrary base, from `pullSection_add_of_finitePresentation` via `map_zsmul`. Mirrors
`EllHom.pullSection_zsmul` (which assumes the noetherian/parked `pullSection_add`). Transports
the `(N : ℤ) • P = 0` killing clause of `IsNaiveGammaOne`/`IsNaiveFullLevel`. -/
theorem pullSection_zsmul_of_finitePresentation (n : ℤ) (P : Y.curve.Section) :
    pullSection R f (n • P) = n • pullSection R f P :=
  map_zsmul (AddMonoidHom.mk' (pullSection R f)
    (pullSection_add_of_finitePresentation R f)) n P

end EllHom

end ModularCurves
