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

/-! ### The divisor-level diagram commute (square, CoordHom-free)

The square `κ₂ ∘ φ = φ_∗ ∘ κ₁` at the **divisor** level: pushing the `(P) − (O)` divisor of
`κ P` through the CoordHom-free place-restriction pushforward gives the `(φ P) − (O)` divisor of
`κ (φ P)`.  This is **pure plumbing**: it uses *only* the basepoint identity
`placeRestrictionPointMap φ 0 = 0` (which is `rfl`), making the `infinity` term land back at
`infinity`.  No CoordHom, no preserves-principal, no place-equality — this mirrors
`pushforwardProjectiveDivisor_kappaDivisor` verbatim with `placeRestrictionPointMap φ` in place of
`φ.toPointMap cd`. -/

/-- **Divisor-level diagram commute (CoordHom-free)**: `φ_∗((P) − (O)) = (φ P) − (O)` for the
place-restriction pushforward.  The basepoint preservation `placeRestrictionPointMap φ 0 = 0`
(definitional) makes the `infinity` term land back at `infinity`. -/
theorem placeRestrictionPushforward_kappaDivisor (φ : HasseWeil.Isogeny W₁ W₂)
    (P : W₁.toAffine.Point) :
    placeRestrictionPushforward φ (Curves.kappaDivisor W₁ P) =
      Curves.kappaDivisor W₂ (placeRestrictionPointMap φ P) := by
  have h_zero : placeRestrictionPointMap φ (0 : W₁.toAffine.Point) = (0 : W₂.toAffine.Point) :=
    placeRestrictionPointMap_zero φ
  unfold Curves.kappaDivisor
  simp only [map_sub, placeRestrictionPushforward_single, placeRestrictionPlaceImage,
    Affine.Point.toProjectiveSmoothPoint_toAffinePoint,
    Curves.ProjectiveSmoothPoint.toAffinePoint_infinity, h_zero,
    Affine.Point.toProjectiveSmoothPoint_zero]

/-! ### The CoordHom-free preserves-principal hypothesis (the genuine wall, isolated)

The **only** input to the CoordHom-free III.4.8 not already proven for elliptic curves is that the
place-restriction pushforward carries *principal* divisors to *principal* divisors (Silverman
II.3.6/II.3.7, the norm–conorm content).  In the CoordHom-gated spine this is
`EC.Isogeny.pushforward_preserves_principal`, proven via the relative norm
`relNorm(m_P) = m_{φP}` — but that proof fundamentally needs the *integral-level* pullback
`Algebra C₂.CoordinateRing C₁.CoordinateRing` packaged by a `CoordHom`, which the place-restriction
construction deliberately avoids.  We isolate it as a named `Prop`.  See the closing report for the
precise state. -/

/-- **The CoordHom-free preserves-principal hypothesis** for a two-curve isogeny `φ`: the
place-restriction pushforward `φ_∗` carries principal projective divisors of `E₁` to principal
projective divisors of `E₂`.  This is the *single* deep input to the CoordHom-free Silverman
III.4.8 below (Silverman II.3.6/II.3.7, norm–conorm). -/
def PlaceRestrictionPreservesPrincipal (φ : HasseWeil.Isogeny W₁ W₂) : Prop :=
  ∀ D : ProjectiveDivisor (⟨W₁⟩ : SmoothPlaneCurve F),
    D ∈ (⟨W₁⟩ : SmoothPlaneCurve F).projPrincipalSubgroup →
    placeRestrictionPushforward φ D ∈ (⟨W₂⟩ : SmoothPlaneCurve F).projPrincipalSubgroup

/-! ### Descent of the CoordHom-free pushforward to Pic⁰ -/

/-- **The CoordHom-free `φ_∗` at the Pic⁰ level**, parametrized by the preserves-principal
hypothesis `h_pres`.  Mirrors `EC.Isogeny.pushforwardPicZeroOfWitness` with
`placeRestrictionPushforward` / `placeRestrictionPushforwardDegZero` in place of the CoordHom-gated
pushforward. -/
noncomputable def placeRestrictionPushforwardPicZero (φ : HasseWeil.Isogeny W₁ W₂)
    (h_pres : PlaceRestrictionPreservesPrincipal φ) :
    SmoothPlaneCurve.PicProj₀ (⟨W₁⟩ : SmoothPlaneCurve F) →+
      SmoothPlaneCurve.PicProj₀ (⟨W₂⟩ : SmoothPlaneCurve F) :=
  QuotientAddGroup.lift
    ((⟨W₁⟩ : SmoothPlaneCurve F).projPrincipalSubgroup.addSubgroupOf
      (ProjectiveDivisor.degZero (⟨W₁⟩ : SmoothPlaneCurve F)))
    ((QuotientAddGroup.mk'
        ((⟨W₂⟩ : SmoothPlaneCurve F).projPrincipalSubgroup.addSubgroupOf
          (ProjectiveDivisor.degZero (⟨W₂⟩ : SmoothPlaneCurve F)))).comp
      (placeRestrictionPushforwardDegZero φ))
    fun D hD => by
      show QuotientAddGroup.mk' _ (placeRestrictionPushforwardDegZero φ D) = 0
      rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      show (placeRestrictionPushforwardDegZero φ D).val ∈
        (⟨W₂⟩ : SmoothPlaneCurve F).projPrincipalSubgroup
      show placeRestrictionPushforward φ D.val ∈
        (⟨W₂⟩ : SmoothPlaneCurve F).projPrincipalSubgroup
      exact h_pres D.val hD

/-- **The Pic⁰-level diagram commute (CoordHom-free)**: `κ₂ (φ P) = φ_∗ (κ₁ P)` on `Pic⁰`,
descending the divisor-level commute `placeRestrictionPushforward_kappaDivisor`.  Mirrors
`EC.Isogeny.picZeroOfPoint_pushforwardPicZero`. -/
theorem picZeroOfPoint_placeRestrictionPushforwardPicZero (φ : HasseWeil.Isogeny W₁ W₂)
    (h_pres : PlaceRestrictionPreservesPrincipal φ) (P : W₁.toAffine.Point) :
    Curves.picZeroOfPoint W₂ (placeRestrictionPointMap φ P) =
      placeRestrictionPushforwardPicZero φ h_pres (Curves.picZeroOfPoint W₁ P) := by
  -- Both sides are `QuotientAddGroup.mk` of degZero-Subtypes whose underlying divisors agree by
  -- `placeRestrictionPushforward_kappaDivisor`.
  show QuotientAddGroup.mk _ = QuotientAddGroup.mk _
  congr 1
  apply Subtype.ext
  exact (placeRestrictionPushforward_kappaDivisor φ P).symm

/-! ### The CoordHom-free Silverman III.4.8 (witness-parametric diagram chase)

The group-hom property of `placeRestrictionPointMap φ`, via the **same Pic⁰ diagram chase** as the
CoordHom-gated `EC.Isogeny.AddHomProperty_of_picZero_witnesses` (HomProperty.lean), with
`placeRestrictionPointMap φ` / `placeRestrictionPushforwardPicZero φ` in place of the CoordHom-gated
maps.  The three curve-side witnesses `h_van_W₁`, `h_van_W₂`, `h_inj_W₁` are identical to the gated
case (they only see `Eᵢ`, not `φ`), and the diagram commute is the pure-plumbing
`picZeroOfPoint_placeRestrictionPushforwardPicZero`.  The *only* `φ`-specific input is the
CoordHom-free preserves-principal hypothesis `h_pres`. -/

/-- **CoordHom-free Silverman III.4.8 (witness-parametric)**: the place-restriction point map
`placeRestrictionPointMap φ` is additive, given
* `h_van_W₁`, `h_van_W₂`: σ vanishes on principal divisors of `E₁`, `E₂` (curve-side, proven for
  elliptic curves via `afInputs_allChar`);
* `h_inj_W₁`: `κ ∘ σ̄ = id` on `Pic⁰(E₁)` (curve-side, ditto);
* `h_pres`: the CoordHom-free preserves-principal hypothesis (the genuine `φ`-specific wall).

The proof is the verbatim diagram chase of `AddHomProperty_of_picZero_witnesses`. -/
theorem placeRestrictionPointMap_add_of_picZero_witnesses (φ : HasseWeil.Isogeny W₁ W₂)
    (h_van_W₁ : ∀ D : ProjectiveDivisor (⟨W₁⟩ : SmoothPlaneCurve F),
      D ∈ (⟨W₁⟩ : SmoothPlaneCurve F).projPrincipalSubgroup →
      Curves.projectiveDivisorSum W₁ D = 0)
    (h_van_W₂ : ∀ D : ProjectiveDivisor (⟨W₂⟩ : SmoothPlaneCurve F),
      D ∈ (⟨W₂⟩ : SmoothPlaneCurve F).projPrincipalSubgroup →
      Curves.projectiveDivisorSum W₂ D = 0)
    (h_pres : PlaceRestrictionPreservesPrincipal φ)
    (h_inj_W₁ : ∀ D : SmoothPlaneCurve.PicProj₀ (⟨W₁⟩ : SmoothPlaneCurve F),
      Curves.picZeroOfPoint W₁
        (HasseWeil.EC.Isogeny.picZeroSumOfWitness W₁ h_van_W₁ D) = D)
    (P Q : W₁.toAffine.Point) :
    placeRestrictionPointMap φ (P + Q) =
      placeRestrictionPointMap φ P + placeRestrictionPointMap φ Q := by
  -- Set up σ̄ at the Pic⁰ level via the witnesses, and the CoordHom-free pushforward at Pic⁰.
  set sb1 := HasseWeil.EC.Isogeny.picZeroSumOfWitness W₁ h_van_W₁ with hsb1_def
  set sb2 := HasseWeil.EC.Isogeny.picZeroSumOfWitness W₂ h_van_W₂ with hsb2_def
  set pushPic := placeRestrictionPushforwardPicZero φ h_pres with hpushPic_def
  -- σ̄ ∘ κ = id (the "easy" direction).
  have h_easy_W₁ : ∀ R : W₁.toAffine.Point, sb1 (Curves.picZeroOfPoint W₁ R) = R :=
    HasseWeil.EC.Isogeny.picZeroSumOfWitness_picZeroOfPoint W₁ h_van_W₁
  have h_easy_W₂ : ∀ R : W₂.toAffine.Point, sb2 (Curves.picZeroOfPoint W₂ R) = R :=
    HasseWeil.EC.Isogeny.picZeroSumOfWitness_picZeroOfPoint W₂ h_van_W₂
  -- Diagram commute at the Pic⁰ level (CoordHom-free).
  have h_diag : ∀ R : W₁.toAffine.Point,
      Curves.picZeroOfPoint W₂ (placeRestrictionPointMap φ R) =
        pushPic (Curves.picZeroOfPoint W₁ R) :=
    picZeroOfPoint_placeRestrictionPushforwardPicZero φ h_pres
  -- σ̄_W₁ is injective (from h_inj_W₁: κ ∘ σ̄ = id).
  have h_sb1_inj : Function.Injective sb1 := by
    intro D₁ D₂ h
    have hh : Curves.picZeroOfPoint W₁ (sb1 D₁) = Curves.picZeroOfPoint W₁ (sb1 D₂) := by rw [h]
    rw [h_inj_W₁ D₁, h_inj_W₁ D₂] at hh
    exact hh
  -- κ_W₁ is additive (σ̄_W₁ injective + σ̄ ∘ κ = id + σ̄ group hom).
  have h_κ_W₁_add : ∀ R₁ R₂ : W₁.toAffine.Point,
      Curves.picZeroOfPoint W₁ (R₁ + R₂) =
        Curves.picZeroOfPoint W₁ R₁ + Curves.picZeroOfPoint W₁ R₂ := by
    intro R₁ R₂
    apply h_sb1_inj
    rw [sb1.map_add, h_easy_W₁, h_easy_W₁, h_easy_W₁]
  -- The chase: a calc chain through sb2 ∘ κ_W₂ = id.
  calc placeRestrictionPointMap φ (P + Q)
      = sb2 (Curves.picZeroOfPoint W₂ (placeRestrictionPointMap φ (P + Q))) :=
        (h_easy_W₂ _).symm
    _ = sb2 (pushPic (Curves.picZeroOfPoint W₁ (P + Q))) := by rw [h_diag]
    _ = sb2 (pushPic (Curves.picZeroOfPoint W₁ P + Curves.picZeroOfPoint W₁ Q)) := by
          rw [h_κ_W₁_add]
    _ = sb2 (pushPic (Curves.picZeroOfPoint W₁ P) + pushPic (Curves.picZeroOfPoint W₁ Q)) := by
          rw [pushPic.map_add]
    _ = sb2 (pushPic (Curves.picZeroOfPoint W₁ P)) +
          sb2 (pushPic (Curves.picZeroOfPoint W₁ Q)) := by rw [sb2.map_add]
    _ = sb2 (Curves.picZeroOfPoint W₂ (placeRestrictionPointMap φ P)) +
          sb2 (Curves.picZeroOfPoint W₂ (placeRestrictionPointMap φ Q)) := by
          rw [← h_diag, ← h_diag]
    _ = placeRestrictionPointMap φ P + placeRestrictionPointMap φ Q := by
          rw [h_easy_W₂, h_easy_W₂]

/-! ### The CoordHom-free Silverman III.4.8, curve-side witnesses discharged (all char)

The curve-side witnesses (`h_van`, `h_inj`) are *not* hypotheses for elliptic curves over `F̄`:
they are discharged uniformly in all characteristics by `Curves.afInputs_allChar` (Miller's
algorithm + the σ-injectivity reduction).  Pulling them in leaves the group-hom property of
`placeRestrictionPointMap φ` resting on the **single** `φ`-specific input
`PlaceRestrictionPreservesPrincipal φ`. -/

/-- **CoordHom-free Silverman III.4.8 (curve-side discharged, all char)**: over an algebraically
closed base, `placeRestrictionPointMap φ` is additive, given *only* the CoordHom-free
preserves-principal hypothesis `h_pres`.  The curve-side `h_van`/`h_inj` witnesses are supplied by
`Curves.afInputs_allChar`. -/
theorem placeRestrictionPointMap_add_of_preservesPrincipal
    [IsDedekindDomain (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsDedekindDomain (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing]
    (φ : HasseWeil.Isogeny W₁ W₂)
    (h_pres : PlaceRestrictionPreservesPrincipal φ)
    (P Q : W₁.toAffine.Point) :
    placeRestrictionPointMap φ (P + Q) =
      placeRestrictionPointMap φ P + placeRestrictionPointMap φ Q := by
  -- Curve-side witnesses from the all-char Abel–Jacobi inputs.
  have h_van_W₁ : ∀ D : ProjectiveDivisor (⟨W₁⟩ : SmoothPlaneCurve F),
      D ∈ (⟨W₁⟩ : SmoothPlaneCurve F).projPrincipalSubgroup →
      Curves.projectiveDivisorSum W₁ D = 0 :=
    (Curves.afInputs_allChar W₁).h_van
      (fun _ hD ↦ SmoothPlaneCurve.principal_mem_degZero (C := ⟨W₁⟩) hD)
  have h_van_W₂ : ∀ D : ProjectiveDivisor (⟨W₂⟩ : SmoothPlaneCurve F),
      D ∈ (⟨W₂⟩ : SmoothPlaneCurve F).projPrincipalSubgroup →
      Curves.projectiveDivisorSum W₂ D = 0 :=
    (Curves.afInputs_allChar W₂).h_van
      (fun _ hD ↦ SmoothPlaneCurve.principal_mem_degZero (C := ⟨W₂⟩) hD)
  have h_inj_W₁ : ∀ D : SmoothPlaneCurve.PicProj₀ (⟨W₁⟩ : SmoothPlaneCurve F),
      Curves.picZeroOfPoint W₁
        (HasseWeil.EC.Isogeny.picZeroSumOfWitness W₁ h_van_W₁ D) = D :=
    (Curves.afInputs_allChar W₁).h_inj h_van_W₁
  exact placeRestrictionPointMap_add_of_picZero_witnesses φ h_van_W₁ h_van_W₂ h_pres h_inj_W₁ P Q

/-! ### Capstone — the realized geometric `HasseWeil.Isogeny` from preserves-principal

Wiring the discharged group-hom property into `placeRestrictionRealization` produces the realized
two-curve `HasseWeil.Isogeny` (stored map = `placeRestrictionPointMap φ`, function-field pullback =
`φ.pullback`) directly from the single CoordHom-free input `PlaceRestrictionPreservesPrincipal φ`.
Its `PullbackEvaluation_twoCurve` coherence is `pullbackEvaluation_twoCurve_placeRestrictionRealization`
(TASK A, already sorry-free), so this is the *complete* CoordHom-free geometric realization of `φ`
modulo the lone preserves-principal wall. -/

/-- **The realized geometric `HasseWeil.Isogeny` of `φ`** (CoordHom-free), given the
preserves-principal hypothesis.  The group-hom property of `placeRestrictionPointMap φ` is supplied
by `placeRestrictionPointMap_add_of_preservesPrincipal`. -/
noncomputable def placeRestrictionRealizationOfPreservesPrincipal
    [IsDedekindDomain (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsDedekindDomain (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing]
    (φ : HasseWeil.Isogeny W₁ W₂)
    (h_pres : PlaceRestrictionPreservesPrincipal φ) :
    HasseWeil.Isogeny W₁ W₂ :=
  placeRestrictionRealization φ
    (placeRestrictionPointMap_add_of_preservesPrincipal φ h_pres)

@[simp] theorem placeRestrictionRealizationOfPreservesPrincipal_pullback
    [IsDedekindDomain (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsDedekindDomain (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing]
    (φ : HasseWeil.Isogeny W₁ W₂)
    (h_pres : PlaceRestrictionPreservesPrincipal φ) :
    (placeRestrictionRealizationOfPreservesPrincipal φ h_pres).pullback = φ.pullback := rfl

@[simp] theorem placeRestrictionRealizationOfPreservesPrincipal_toAddMonoidHom_apply
    [IsDedekindDomain (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsDedekindDomain (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing]
    (φ : HasseWeil.Isogeny W₁ W₂)
    (h_pres : PlaceRestrictionPreservesPrincipal φ) (P : W₁.toAffine.Point) :
    (placeRestrictionRealizationOfPreservesPrincipal φ h_pres).toAddMonoidHom P =
      placeRestrictionPointMap φ P := rfl

end HasseWeil.WeilPairing
