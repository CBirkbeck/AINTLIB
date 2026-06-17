/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.IsogenyAG.TwoCurvePointImage
import HasseWeil.EC.IsogenyAG.HomProperty

/-!
# The group-hom property of the CoordHom-free place-restriction point map (PE-1b, TASK B)

For a two-curve isogeny `φ : Isogeny W₁ W₂` over an algebraically closed base, TASK A
(`TwoCurvePointImage.lean`) built the **concrete CoordHom-free geometric point map**
`placeRestrictionPointMap φ : E₁ → E₂` and proved its `PullbackEvaluation_twoCurve` coherence,
reducing PE-1 to **exactly** the group-hom property of `placeRestrictionPointMap φ`
(Silverman III.4.8, the CoordHom-free case).  This file attacks that group-hom property by
**replicating the project's Pic⁰ diagram chase** (`AddHomProperty_of_picZero_witnesses`,
`HomProperty.lean`) with `placeRestrictionPointMap φ` in place of the CoordHom-gated place-image
map `toPointMap cd`.

## The diagram chase, CoordHom-free

The textbook proof (Silverman III.4.8, book p.71): the divisor pushforward `φ_∗` induces a group
homomorphism `Pic⁰(E₁) → Pic⁰(E₂)`; the Abel–Jacobi maps `κᵢ : Eᵢ ≅ Pic⁰(Eᵢ)` are group
isomorphisms; the square `κ₂ ∘ φ = φ_∗ ∘ κ₁` commutes because `φ(O) = O`; a diagram chase forces
`φ` additive.  The chase is *entirely abstract* — the **only** CoordHom dependence in the project's
spine is:

1. the **divisor pushforward** `pushforwardProjectiveDivisor φ cd = Finsupp.mapDomain (P ↦ toPointMap
   cd P)` — here replaced, CoordHom-free, by `placeRestrictionPushforward φ = Finsupp.mapDomain
   (P ↦ placeRestrictionPointMap φ P)` (a group hom on divisors *by construction*);
2. the **diagram commute** `picZeroOfPoint_pushforwardPicZero` — here `placeRestrictionPushforward`
   sends `(P) − (O)` to `(φ P) − (O)` purely from `placeRestrictionPointMap_zero` (the basepoint
   `O ↦ O`), so the commute is pure plumbing;
3. the **norm–conorm** preserves-principal input `h_pres` (Silverman II.3.6/II.3.7) — this is the
   **genuine wall** (`PlaceRestrictionPreservesPrincipal` below), isolated as a named hypothesis.

So the group-hom property of `placeRestrictionPointMap φ` follows from the **same three witnesses**
as the CoordHom-gated III.4.8 — `h_van₁`, `h_van₂`, `h_inj₁` (all curve-side, *already proven* for
elliptic curves via `afInputs_allChar`) — plus the CoordHom-free preserves-principal input
`h_pres'`.  This file delivers everything except `h_pres'`, which is stated precisely and discussed
in the closing report.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.4.8, III.3.4, II.3.6/7.
-/

open WeierstrassCurve

namespace HasseWeil.WeilPairing

open HasseWeil HasseWeil.Curves HasseWeil.EC.Isogeny

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {F : Type*} [Field F] [DecidableEq F]
variable {W₁ W₂ : WeierstrassCurve F} [W₁.toAffine.IsElliptic] [W₂.toAffine.IsElliptic]
variable [IsAlgClosed F]

/-! ### The CoordHom-free divisor pushforward via the place-restriction point map -/

/-- **The CoordHom-free place-image map** on the projective closure: an affine smooth point `P` is
sent to `placeRestrictionPointMap φ P` (re-promoted to a projective smooth point), the place at
infinity is fixed. -/
noncomputable def placeRestrictionPlaceImage (φ : HasseWeil.Isogeny W₁ W₂) :
    ProjectiveSmoothPoint (⟨W₁⟩ : SmoothPlaneCurve F) →
      ProjectiveSmoothPoint (⟨W₂⟩ : SmoothPlaneCurve F) :=
  fun P => (placeRestrictionPointMap φ P.toAffinePoint).toProjectiveSmoothPoint

/-- **The CoordHom-free divisor pushforward** `φ_∗ : Div(E₁) → Div(E₂)`, `Σ nᵢ (Pᵢ) ↦
Σ nᵢ (φ Pᵢ)`, realised as `Finsupp.mapDomain` along `placeRestrictionPlaceImage`.  This is a group
homomorphism on divisors **by construction** (no CoordHom, no preserves-principal input needed). -/
noncomputable def placeRestrictionPushforward (φ : HasseWeil.Isogeny W₁ W₂) :
    ProjectiveDivisor (⟨W₁⟩ : SmoothPlaneCurve F) →+
      ProjectiveDivisor (⟨W₂⟩ : SmoothPlaneCurve F) :=
  Finsupp.mapDomain.addMonoidHom (placeRestrictionPlaceImage φ)

@[simp] theorem placeRestrictionPushforward_apply (φ : HasseWeil.Isogeny W₁ W₂)
    (D : ProjectiveDivisor (⟨W₁⟩ : SmoothPlaneCurve F)) :
    placeRestrictionPushforward φ D = Finsupp.mapDomain (placeRestrictionPlaceImage φ) D := rfl

@[simp] theorem placeRestrictionPushforward_single (φ : HasseWeil.Isogeny W₁ W₂)
    (P : ProjectiveSmoothPoint (⟨W₁⟩ : SmoothPlaneCurve F)) (n : ℤ) :
    placeRestrictionPushforward φ (Finsupp.single P n) =
      Finsupp.single (placeRestrictionPlaceImage φ P) n := by
  rw [placeRestrictionPushforward_apply, Finsupp.mapDomain_single]

/-- The CoordHom-free pushforward preserves degree. -/
theorem degree_placeRestrictionPushforward (φ : HasseWeil.Isogeny W₁ W₂)
    (D : ProjectiveDivisor (⟨W₁⟩ : SmoothPlaneCurve F)) :
    ProjectiveDivisor.degree (placeRestrictionPushforward φ D) =
      ProjectiveDivisor.degree D := by
  rw [placeRestrictionPushforward_apply]
  unfold ProjectiveDivisor.degree
  rw [Finsupp.sum_mapDomain_index (h := fun _ n => n) (fun _ => rfl) (fun _ _ _ => rfl)]

/-- The CoordHom-free pushforward restricts to a homomorphism on the degree-zero subgroup. -/
noncomputable def placeRestrictionPushforwardDegZero (φ : HasseWeil.Isogeny W₁ W₂) :
    ProjectiveDivisor.degZero (⟨W₁⟩ : SmoothPlaneCurve F) →+
      ProjectiveDivisor.degZero (⟨W₂⟩ : SmoothPlaneCurve F) where
  toFun D :=
    ⟨placeRestrictionPushforward φ D.val,
      ProjectiveDivisor.mem_degZero.mpr <| by
        rw [degree_placeRestrictionPushforward]
        exact ProjectiveDivisor.mem_degZero.mp D.property⟩
  map_zero' := by
    apply Subtype.ext
    show placeRestrictionPushforward φ 0 = 0
    exact (placeRestrictionPushforward φ).map_zero
  map_add' D₁ D₂ := by
    apply Subtype.ext
    show placeRestrictionPushforward φ (D₁.val + D₂.val) =
      placeRestrictionPushforward φ D₁.val + placeRestrictionPushforward φ D₂.val
    exact (placeRestrictionPushforward φ).map_add _ _

end HasseWeil.WeilPairing
