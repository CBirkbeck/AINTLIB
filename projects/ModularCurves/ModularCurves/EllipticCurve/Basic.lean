import ModularCurves.EllipticCurve.WeierstrassModel
import Mathlib.AlgebraicGeometry.Fiber

/-!
# Elliptic curves over a base scheme

The central definition of the project. Following the standard definition
(KM 2.1.1; Deligne–Rapoport II.1.1; Loeffler §3.3 Def 3.3.1, verbatim: *"An elliptic curve
over `S` is a scheme `ℰ` with a morphism `π : ℰ → S` (an `S`-scheme) such that `π` is proper
and flat and all fibres are smooth genus 1 curves, given with a section `0 : S → ℰ`"*):

> An **elliptic curve over a scheme `S`** is a morphism `π : E ⟶ S` which is smooth of
> relative dimension 1 and proper, together with a section `0 : S ⟶ E`, such that every
> fibre is a geometrically connected curve of genus 1.

## The genus-1 fibre condition

Mathlib has no coherent cohomology yet, so "genus 1" is not directly expressible. We use the
classical equivalent (Riemann–Roch over a field, black-boxed — Silverman III.3.1): *a pointed
smooth proper geometrically connected genus-1 curve over a field `k` is exactly a pointed
plane Weierstrass cubic with unit discriminant.* The fibre condition below therefore asks
each fibre, with the point induced by the zero section, to be a Weierstrass model of some
elliptic Weierstrass curve over the residue field. Once mathlib acquires cohomology, the
equivalence with the genus formulation becomes theorem `fibre_condition_iff_genus_one`
(ticket `T-A9`, statement deferred until `genus` exists — see plan.md, API gap AG-COH).

## Design notes (reviewed decisions — see REVIEW_BRIEF Q1, Q2)

* **No group structure in the definition.** All sources define an elliptic curve as pure
  geometry; the group law is a *theorem* (KM 2.1.2, via `Pic⁰` — Abel). It enters in
  `GroupLaw.lean` as a registered construction, never as a definitional field.
* The smoothness field implies flatness + local finite presentation, so this agrees with
  Loeffler's "proper and flat with smooth fibres" phrasing (his Def 3.4.1).
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

/-- The point of the fibre `π.fiber s` induced by a section `z : S ⟶ E` of `π`. -/
noncomputable def sectionFiberPoint {E S : Scheme.{u}} (π : E ⟶ S) (z : S ⟶ E)
    (hz : z ≫ π = 𝟙 S) (s : S) : Spec (S.residueField s) ⟶ π.fiber s :=
  pullback.lift (S.fromSpecResidueField s ≫ z) (𝟙 _)
    (by simp [Category.assoc, hz])

/-- **The fibre condition**: every fibre of `π`, pointed by the zero section, is a
Weierstrass model of some elliptic (unit-discriminant) Weierstrass curve over the residue
field. By Riemann–Roch over a field (black box; Silverman III.3.1) this is equivalent to:
every fibre is a smooth proper geometrically connected genus-1 curve.
Source: Loeffler Def 3.3.1; KM 2.1.1. -/
def FibrewiseElliptic {E S : Scheme.{u}} (π : E ⟶ S) (z : S ⟶ E) (hz : z ≫ π = 𝟙 S) : Prop :=
  ∀ s : S, ∃ W : WeierstrassCurve (S.residueField s), W.IsElliptic ∧
    IsWeierstrassModel W (π.fiber s) (π.fiberToSpecResidueField s)
      (sectionFiberPoint π z hz s)

/-- An **elliptic curve over the scheme `S`**: a smooth proper relative curve with a section
whose fibres are (pointed) genus-1 curves, the latter expressed via `FibrewiseElliptic`.

Source: KM 2.1.1; Deligne–Rapoport II.1.1; Loeffler Def 3.3.1. -/
structure EllipticCurve (S : Scheme.{u}) where
  /-- The total space. -/
  E : Scheme.{u}
  /-- The structure morphism. -/
  π : E ⟶ S
  /-- The zero section. -/
  zero : S ⟶ E
  zero_π : zero ≫ π = 𝟙 S
  smooth : SmoothOfRelativeDimension 1 π
  proper : IsProper π
  fibres : FibrewiseElliptic π zero zero_π

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

attribute [instance] EllipticCurve.smooth EllipticCurve.proper

/-- The `T`-points of `E/S` along `g : T ⟶ S`: sections of the pullback, i.e. morphisms
`T ⟶ E` lifting `g`. `E.Point (𝟙 S)`-style specialisations give `E(S)`.
Source: Loeffler §3.3: "`ℰ(S) = Hom_{S−Sch}(S, ℰ)` are the sections of `π` picking out a
point on each fibre." -/
abbrev Point {T : Scheme.{u}} (g : T ⟶ S) : Type u :=
  { h : T ⟶ E.E // h ≫ E.π = g }

/-- The zero `T`-point. -/
def zeroPoint {T : Scheme.{u}} (g : T ⟶ S) : E.Point g :=
  ⟨g ≫ E.zero, by rw [Category.assoc, E.zero_π, Category.comp_id]⟩

/-- **(T-A5)** Base change: an elliptic curve over `S` pulls back to an elliptic curve over
`T` along any `g : T ⟶ S`. The total space is the fibre product `E ×_S T`; smoothness and
properness are stable under base change (mathlib instances); the fibre condition transports
along the residue-field embeddings. Source: KM 2.1 (elliptic curves form a category fibred
over schemes); Loeffler §3.7. -/
noncomputable def baseChange {T : Scheme.{u}} (g : T ⟶ S) : EllipticCurve T where
  E := pullback E.π g
  π := pullback.snd E.π g
  zero := pullback.lift (g ≫ E.zero) (𝟙 T)
    (by rw [Category.assoc, E.zero_π, Category.comp_id, Category.id_comp])
  zero_π := pullback.lift_snd _ _ _
  smooth := by sorry
  proper := by sorry
  fibres := by sorry

end EllipticCurve

end ModularCurves
