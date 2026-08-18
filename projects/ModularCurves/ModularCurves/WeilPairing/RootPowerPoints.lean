/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.RootSplitting

/-!
# Root-powers on points, and the exponent step of `hdet` (route β, item (B))

`hdet` (`WeilPairing/DetCocycle.lean`) compares two composites
`γ ≫ rootPower N ζ k ≫ muNMapAlong p N`. Both are `W`-points of `μ_{N,S}` — *not* of `μ_{N,S'}` — and
their structure maps to `S` agree, because the two projections of the kernel pair agree after `→ S`.
So the comparison can be made by **values**, and the two lemmas that compute those values already
exist in `GroupScheme/MuN.lean`:

* `muNPointsEquiv_mapAlong` — the base-change comparison `muNMapAlong` does not change the value;
* `muNPointsEquiv_natural` — restriction along `k` acts on values by `Γ.map k.op`.

Together with `rootPower`'s definition (the point with value `ζ ^ k.val`) this reduces `hdet`'s
exponent step to a single equation in `Γ(W, ⊤)`.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

variable {S' S : Scheme.{u}} (N : ℕ) [NeZero N]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The value of `rootPower N ζ k` is `ζ ^ k.val` — `rootPower` is by definition the point
`muNPointsEquiv` sends to that root of unity. -/
theorem muNPointsEquiv_rootPower (ζ : { a : Γ(S', (⊤ : S'.Opens)) // a ^ N = 1 }) (k : ZMod N) :
    (muNPointsEquiv S' N (𝟙 S') ⟨rootPower N ζ k, rootPower_π N ζ k⟩ :
        Γ(S', (⊤ : S'.Opens))) =
      (ζ : Γ(S', (⊤ : S'.Opens))) ^ k.val := by
  have h : (⟨rootPower N ζ k, rootPower_π N ζ k⟩ :
      { h : S' ⟶ muN S' N // h ≫ muNπ S' N = 𝟙 S' }) =
      (muNPointsEquiv S' N (𝟙 S')).symm
        ⟨(ζ : Γ(S', (⊤ : S'.Opens))) ^ k.val, by
          rw [← pow_mul, mul_comm, pow_mul, ζ.2, one_pow]⟩ := Subtype.ext rfl
  rw [h, Equiv.apply_symm_apply]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The value of a pulled-back root-power on the cover itself: `Γ(γ)(ζ) ^ k.val`.

The base map is taken as a variable `q` with `hq : γ ≫ 𝟙 S' = q`, so that `subst` can align it with
the index `k ≫ g` that `muNPointsEquiv_natural` produces — `γ ≫ 𝟙 S' = γ` is a category axiom, not
`rfl`, and rewriting it inside the equiv's index is not type-correct. -/
theorem muNPointsEquiv_comp_rootPower {W : Scheme.{u}}
    (ζ : { a : Γ(S', (⊤ : S'.Opens)) // a ^ N = 1 }) (γ : W ⟶ S') (k : ZMod N) {q : W ⟶ S'}
    (hq : γ ≫ 𝟙 S' = q) (hv : (γ ≫ rootPower N ζ k) ≫ muNπ S' N = q) :
    (muNPointsEquiv S' N q ⟨γ ≫ rootPower N ζ k, hv⟩ : Γ(W, (⊤ : W.Opens))) =
      (Scheme.Γ.map γ.op).hom (ζ : Γ(S', (⊤ : S'.Opens))) ^ k.val := by
  subst hq
  exact (muNPointsEquiv_natural S' N (𝟙 S') γ ⟨rootPower N ζ k, rootPower_π N ζ k⟩).trans
    ((congrArg (Scheme.Γ.map γ.op).hom (muNPointsEquiv_rootPower N ζ k)).trans (map_pow _ _ _))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The value of a pulled-back root-power, pushed forward along the cover: `Γ(γ)(ζ) ^ k.val`.

`muNPointsEquiv_mapAlong` (the base-change comparison preserves values) followed by
`muNPointsEquiv_natural` (restriction acts by `Γ.map`) and `muNPointsEquiv_rootPower`. The chain is
threaded with `Eq.trans`, not `rw`: `muNPointsEquiv_mapAlong` bakes a specific section-condition proof
term into its statement, and proof terms are defeq but not syntactically equal. -/
theorem muNPointsEquiv_comp_rootPower_mapAlong {W : Scheme.{u}} (p : S' ⟶ S)
    (ζ : { a : Γ(S', (⊤ : S'.Opens)) // a ^ N = 1 }) (γ : W ⟶ S') (k : ZMod N)
    (hw : ((γ ≫ rootPower N ζ k) ≫ muNMapAlong p N) ≫ muNπ S N = γ ≫ p) :
    (muNPointsEquiv S N (γ ≫ p) ⟨(γ ≫ rootPower N ζ k) ≫ muNMapAlong p N, hw⟩ :
        Γ(W, (⊤ : W.Opens))) =
      (Scheme.Γ.map γ.op).hom (ζ : Γ(S', (⊤ : S'.Opens))) ^ k.val := by
  have hv : (γ ≫ rootPower N ζ k) ≫ muNπ S' N = γ := by
    rw [Category.assoc, rootPower_π, Category.comp_id]
  exact (muNPointsEquiv_mapAlong p N γ ⟨γ ≫ rootPower N ζ k, hv⟩).trans
    (muNPointsEquiv_comp_rootPower N ζ γ k (Category.comp_id γ) hv)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- …the same, read at any base map equal to `γ ≫ p`, so that two different points of the cover lying
over the same point of the base can be compared inside one fibre. -/
theorem muNPointsEquiv_comp_rootPower_mapAlong_of_eq {W : Scheme.{u}} (p : S' ⟶ S)
    (ζ : { a : Γ(S', (⊤ : S'.Opens)) // a ^ N = 1 }) (γ : W ⟶ S') (k : ZMod N) {q : W ⟶ S}
    (hq : γ ≫ p = q) (hw : ((γ ≫ rootPower N ζ k) ≫ muNMapAlong p N) ≫ muNπ S N = q) :
    (muNPointsEquiv S N q ⟨(γ ≫ rootPower N ζ k) ≫ muNMapAlong p N, hw⟩ :
        Γ(W, (⊤ : W.Opens))) =
      (Scheme.Γ.map γ.op).hom (ζ : Γ(S', (⊤ : S'.Opens))) ^ k.val := by
  subst hq
  exact muNPointsEquiv_comp_rootPower_mapAlong N p ζ γ k hw

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **(route β, item (B))** Two pulled-back root-powers, pushed forward along the cover, agree as soon
as their **values** agree — an equation in `Γ(W, ⊤)`.

This is `hdet`'s exponent step: `hp` says the two points of the cover lie over the same point of the
base (true for the two projections of the kernel pair, which agree after `→ S`), so both sides lie in
the same fibre of `muNPointsEquiv S N (α ≫ p)` and may be compared by value; `hval` is the determinant
law of the root, raised to the relevant exponent. -/
theorem comp_rootPower_muNMapAlong_eq {W : Scheme.{u}} (p : S' ⟶ S)
    (ζ : { a : Γ(S', (⊤ : S'.Opens)) // a ^ N = 1 }) (α β : W ⟶ S') (m m' : ZMod N)
    (hp : α ≫ p = β ≫ p)
    (hval : (Scheme.Γ.map α.op).hom (ζ : Γ(S', (⊤ : S'.Opens))) ^ m.val =
      (Scheme.Γ.map β.op).hom (ζ : Γ(S', (⊤ : S'.Opens))) ^ m'.val) :
    α ≫ rootPower N ζ m ≫ muNMapAlong p N = β ≫ rootPower N ζ m' ≫ muNMapAlong p N := by
  have hover : ∀ (γ : W ⟶ S') (k : ZMod N),
      ((γ ≫ rootPower N ζ k) ≫ muNMapAlong p N) ≫ muNπ S N = γ ≫ p := by
    intro γ k
    rw [Category.assoc, Category.assoc, muNMapAlong_π, ← Category.assoc (rootPower N ζ k),
      rootPower_π, Category.id_comp]
  have hoverβ : ((β ≫ rootPower N ζ m') ≫ muNMapAlong p N) ≫ muNπ S N = α ≫ p := by
    rw [hover β m', hp]
  have key : (⟨(α ≫ rootPower N ζ m) ≫ muNMapAlong p N, hover α m⟩ :
      { h : W ⟶ muN S N // h ≫ muNπ S N = α ≫ p }) =
      ⟨(β ≫ rootPower N ζ m') ≫ muNMapAlong p N, hoverβ⟩ := by
    refine (muNPointsEquiv S N (α ≫ p)).injective (Subtype.ext ?_)
    refine (muNPointsEquiv_comp_rootPower_mapAlong_of_eq N p ζ α m rfl (hover α m)).trans ?_
    exact hval.trans
      (muNPointsEquiv_comp_rootPower_mapAlong_of_eq N p ζ β m' hp.symm hoverβ).symm
  have := congrArg Subtype.val key
  simpa only [Category.assoc] using this

end ModularCurves
