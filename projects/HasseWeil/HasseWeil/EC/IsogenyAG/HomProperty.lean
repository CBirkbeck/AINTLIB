import HasseWeil.Curves.PicZero
import HasseWeil.Curves.PicZeroPushforward

/-!
# Universal Silverman III.4.8 (Pic⁰ route, witness-parametric)

This file builds the **witness-parametric** form of the universal
`AddHomProperty` for the new `Isogeny.AG` structure: every isogeny is a
group homomorphism on K-rational points (Silverman III.4.8).

The proof follows Silverman's textbook argument (page 71): induce
`φ_∗ : Pic⁰(E₁) → Pic⁰(E₂)` by functoriality, use `κ : E ≅ Pic⁰(E)`
(Silverman III.3.4), and observe that the diagram commutes since `φ(O) = O`.

The "witnesses" parametrizing the framework are exactly the open / blocked
tickets in `.mathlib-quality/tickets/picard/`:
* `T-PIC-A-002` — σ vanishes on principal divisors.
* `T-PIC-C-003` — pushforward preserves principal divisors.
* `T-III-3-003` (worker-K) — κ is injective via `(P) ~ (Q) ⇒ P = Q`.

Once any of these land, the corresponding witness becomes provable, and
the universal AddHomProperty drops in unconditionally for the
discharged setting.

## Main definitions

* `Isogeny.picZeroSumOfWitness` — descent of σ̄ to `Pic⁰` given the
  vanishing-on-principal witness.
* `Isogeny.pushforwardPicZeroOfWitness` — descent of φ_∗ to `Pic⁰` given
  the preserves-principal witness.
* `Isogeny.AddHomProperty_of_picZero_witnesses` — the universal
  AddHomProperty given all three witnesses.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], III.3.4, III.4.8.
-/

open WeierstrassCurve

namespace HasseWeil.EC.Isogeny

variable {F : Type*} [Field F] [DecidableEq F]

/-! ### Descent of σ̄ to Pic⁰ given the vanishing-on-principal witness -/

/-- The σ̄ map at the `Pic⁰` level, parametrized by the vanishing-on-principal
witness (`T-PIC-A-002`). Closes `T-PIC-A-003` and `T-PIC-A-004`
witness-parametrically. -/
noncomputable def picZeroSumOfWitness
    (W : Affine F) [W.IsElliptic]
    (h_van : ∀ D : Curves.ProjectiveDivisor (⟨W⟩ : Curves.SmoothPlaneCurve F),
      D ∈ (⟨W⟩ : Curves.SmoothPlaneCurve F).projPrincipalSubgroup →
      Curves.projectiveDivisorSum W D = 0) :
    Curves.SmoothPlaneCurve.PicProj₀ (⟨W⟩ : Curves.SmoothPlaneCurve F) →+
      W.Point :=
  let restricted :
      Curves.ProjectiveDivisor.degZero (⟨W⟩ : Curves.SmoothPlaneCurve F) →+
        W.Point :=
    (Curves.projectiveDivisorSumHom W).comp
      (Curves.ProjectiveDivisor.degZero (⟨W⟩ : Curves.SmoothPlaneCurve F)).subtype
  QuotientAddGroup.lift
    ((⟨W⟩ : Curves.SmoothPlaneCurve F).projPrincipalSubgroup.addSubgroupOf
      (Curves.ProjectiveDivisor.degZero (⟨W⟩ : Curves.SmoothPlaneCurve F)))
    restricted
    fun D hD ↦ by
      -- D ∈ addSubgroupOf means D.val ∈ projPrincipalSubgroup
      -- Apply h_van.
      show Curves.projectiveDivisorSum W D.val = 0
      exact h_van D.val hD

@[simp] theorem picZeroSumOfWitness_apply_mk
    (W : Affine F) [W.IsElliptic]
    (h_van : ∀ D : Curves.ProjectiveDivisor (⟨W⟩ : Curves.SmoothPlaneCurve F),
      D ∈ (⟨W⟩ : Curves.SmoothPlaneCurve F).projPrincipalSubgroup →
      Curves.projectiveDivisorSum W D = 0)
    (D : Curves.ProjectiveDivisor.degZero
      (⟨W⟩ : Curves.SmoothPlaneCurve F)) :
    picZeroSumOfWitness W h_van (QuotientAddGroup.mk D) =
      Curves.projectiveDivisorSum W D.val := rfl

/-- σ̄ ∘ κ = id at the Pic⁰ level (the "easy" direction). Inherits the
divisor-level fact `projectiveDivisorSum_kappaDivisor`. -/
@[simp] theorem picZeroSumOfWitness_picZeroOfPoint
    (W : Affine F) [W.IsElliptic]
    (h_van : ∀ D : Curves.ProjectiveDivisor (⟨W⟩ : Curves.SmoothPlaneCurve F),
      D ∈ (⟨W⟩ : Curves.SmoothPlaneCurve F).projPrincipalSubgroup →
      Curves.projectiveDivisorSum W D = 0)
    (P : W.Point) :
    picZeroSumOfWitness W h_van (Curves.picZeroOfPoint W P) = P := by
  unfold Curves.picZeroOfPoint
  rw [picZeroSumOfWitness_apply_mk]
  exact Curves.projectiveDivisorSum_kappaDivisor W P

/-! ### Descent of pushforward to Pic⁰ given the preserves-principal witness -/

variable {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- The φ_∗ map at the `Pic⁰` level for an isogeny, parametrized by the
preserves-principal witness (`T-PIC-C-003`). Closes `T-PIC-C-004`
witness-parametrically. -/
noncomputable def pushforwardPicZeroOfWitness
    (φ : Isogeny W₁ W₂) (cd : φ.toCurveMap.CoordHom)
    (h_pres : ∀ D : Curves.ProjectiveDivisor (⟨W₁⟩ : Curves.SmoothPlaneCurve F),
      D ∈ (⟨W₁⟩ : Curves.SmoothPlaneCurve F).projPrincipalSubgroup →
      pushforwardProjectiveDivisor φ cd D ∈
        (⟨W₂⟩ : Curves.SmoothPlaneCurve F).projPrincipalSubgroup) :
    Curves.SmoothPlaneCurve.PicProj₀ (⟨W₁⟩ : Curves.SmoothPlaneCurve F) →+
      Curves.SmoothPlaneCurve.PicProj₀ (⟨W₂⟩ : Curves.SmoothPlaneCurve F) :=
  QuotientAddGroup.lift
    ((⟨W₁⟩ : Curves.SmoothPlaneCurve F).projPrincipalSubgroup.addSubgroupOf
      (Curves.ProjectiveDivisor.degZero (⟨W₁⟩ : Curves.SmoothPlaneCurve F)))
    ((QuotientAddGroup.mk'
        ((⟨W₂⟩ : Curves.SmoothPlaneCurve F).projPrincipalSubgroup.addSubgroupOf
          (Curves.ProjectiveDivisor.degZero
            (⟨W₂⟩ : Curves.SmoothPlaneCurve F)))).comp
      (pushforwardDegZero φ cd))
    fun D hD ↦ by
      -- Goal: comp ((mk' N₂).comp (pushforwardDegZero φ cd)) D = 0
      -- Strategy: the comp at D produces Quotient.mk of (pushforwardDegZero φ cd D),
      -- and we show this is zero via mk_eq_zero_iff and h_pres.
      show QuotientAddGroup.mk' _ (pushforwardDegZero φ cd D) = 0
      rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      show (pushforwardDegZero φ cd D).val ∈
        (⟨W₂⟩ : Curves.SmoothPlaneCurve F).projPrincipalSubgroup
      show pushforwardProjectiveDivisor φ cd D.val ∈
        (⟨W₂⟩ : Curves.SmoothPlaneCurve F).projPrincipalSubgroup
      exact h_pres D.val hD

/-! ### Diagram commute at the Pic⁰ level (T-PIC-D-001) -/

/-- The Pic⁰-level diagram commute, descending the divisor-level commute
`pushforwardProjectiveDivisor_kappaDivisor`. Closes T-PIC-D-001
witness-parametrically. -/
theorem picZeroOfPoint_pushforwardPicZero
    (φ : Isogeny W₁ W₂) (cd : φ.toCurveMap.CoordHom)
    (h_pres : ∀ D : Curves.ProjectiveDivisor (⟨W₁⟩ : Curves.SmoothPlaneCurve F),
      D ∈ (⟨W₁⟩ : Curves.SmoothPlaneCurve F).projPrincipalSubgroup →
      pushforwardProjectiveDivisor φ cd D ∈
        (⟨W₂⟩ : Curves.SmoothPlaneCurve F).projPrincipalSubgroup)
    (P : W₁.Point) :
    Curves.picZeroOfPoint W₂ (φ.toPointMap cd P) =
      pushforwardPicZeroOfWitness φ cd h_pres
        (Curves.picZeroOfPoint W₁ P) := by
  -- Both sides are `QuotientAddGroup.mk` of degZero-Subtypes whose
  -- underlying divisors agree by `pushforwardProjectiveDivisor_kappaDivisor`.
  -- Reduce to Subtype equality, then to divisor equality.
  show QuotientAddGroup.mk _ = QuotientAddGroup.mk _
  congr 1
  apply Subtype.ext
  exact (pushforwardProjectiveDivisor_kappaDivisor φ cd P).symm

/-! ### Universal AddHomProperty given all witnesses (T-PIC-E-001) -/

/-- **B-4-003 witness-parametric closure**: the universal `AddHomProperty`
follows from three witnesses corresponding to the three open / blocked
tickets:
* `h_van_W₁`, `h_van_W₂`: σ vanishes on principal divisors (T-PIC-A-002).
* `h_pres`: pushforward preserves principal divisors (T-PIC-C-003).
* `h_inj_W₁`: σ̄ is injective on Pic⁰(W₁) (= `κ ∘ σ̄ = id`, gated on
  worker-K's T-III-3-003).

When all three land, instantiating yields the unconditional
B-4-003. -/
theorem AddHomProperty_of_picZero_witnesses
    (φ : Isogeny W₁ W₂) (cd : φ.toCurveMap.CoordHom)
    (h_van_W₁ : ∀ D : Curves.ProjectiveDivisor (⟨W₁⟩ : Curves.SmoothPlaneCurve F),
      D ∈ (⟨W₁⟩ : Curves.SmoothPlaneCurve F).projPrincipalSubgroup →
      Curves.projectiveDivisorSum W₁ D = 0)
    (h_van_W₂ : ∀ D : Curves.ProjectiveDivisor (⟨W₂⟩ : Curves.SmoothPlaneCurve F),
      D ∈ (⟨W₂⟩ : Curves.SmoothPlaneCurve F).projPrincipalSubgroup →
      Curves.projectiveDivisorSum W₂ D = 0)
    (h_pres : ∀ D : Curves.ProjectiveDivisor (⟨W₁⟩ : Curves.SmoothPlaneCurve F),
      D ∈ (⟨W₁⟩ : Curves.SmoothPlaneCurve F).projPrincipalSubgroup →
      pushforwardProjectiveDivisor φ cd D ∈
        (⟨W₂⟩ : Curves.SmoothPlaneCurve F).projPrincipalSubgroup)
    (h_inj_W₁ : ∀ D : Curves.SmoothPlaneCurve.PicProj₀
        (⟨W₁⟩ : Curves.SmoothPlaneCurve F),
      Curves.picZeroOfPoint W₁
        (picZeroSumOfWitness W₁ h_van_W₁ D) = D) :
    φ.AddHomProperty cd := by
  -- Set up the σ̄ and pushforward at Pic⁰ level via the witnesses.
  set sb1 := picZeroSumOfWitness W₁ h_van_W₁ with hsb1_def
  set sb2 := picZeroSumOfWitness W₂ h_van_W₂ with hsb2_def
  set pushPic := pushforwardPicZeroOfWitness φ cd h_pres with hpushPic_def
  -- σ̄ ∘ κ = id (the "easy" direction we have).
  have h_easy_W₁ : ∀ R : W₁.Point,
      sb1 (Curves.picZeroOfPoint W₁ R) = R :=
    picZeroSumOfWitness_picZeroOfPoint W₁ h_van_W₁
  have h_easy_W₂ : ∀ R : W₂.Point,
      sb2 (Curves.picZeroOfPoint W₂ R) = R :=
    picZeroSumOfWitness_picZeroOfPoint W₂ h_van_W₂
  -- Diagram commute at Pic⁰ level.
  have h_diag : ∀ R : W₁.Point,
      Curves.picZeroOfPoint W₂ (φ.toPointMap cd R) =
        pushPic (Curves.picZeroOfPoint W₁ R) :=
    picZeroOfPoint_pushforwardPicZero φ cd h_pres
  -- σ̄_W₁ is injective (from h_inj_W₁: κ ∘ σ̄ = id, so σ̄ has a left inverse).
  have h_sb1_inj : Function.Injective sb1 := by
    intro D₁ D₂ h
    have hh : Curves.picZeroOfPoint W₁ (sb1 D₁) =
        Curves.picZeroOfPoint W₁ (sb1 D₂) := by rw [h]
    rw [h_inj_W₁ D₁, h_inj_W₁ D₂] at hh
    exact hh
  -- κ_W₁ is additive (derived from σ̄_W₁ injective + σ̄ ∘ κ = id + σ̄ group hom).
  have h_κ_W₁_add : ∀ R₁ R₂ : W₁.Point,
      Curves.picZeroOfPoint W₁ (R₁ + R₂) =
        Curves.picZeroOfPoint W₁ R₁ + Curves.picZeroOfPoint W₁ R₂ := by
    intro R₁ R₂
    apply h_sb1_inj
    rw [sb1.map_add, h_easy_W₁, h_easy_W₁, h_easy_W₁]
  -- Now the AddHomProperty proof: a calc chain through sb2 ∘ κ_W₂ = id.
  intro P Q
  calc φ.toPointMap cd (P + Q)
      = sb2 (Curves.picZeroOfPoint W₂ (φ.toPointMap cd (P + Q))) :=
        (h_easy_W₂ _).symm
    _ = sb2 (pushPic (Curves.picZeroOfPoint W₁ (P + Q))) := by rw [h_diag]
    _ = sb2 (pushPic (Curves.picZeroOfPoint W₁ P +
            Curves.picZeroOfPoint W₁ Q)) := by rw [h_κ_W₁_add]
    _ = sb2 (pushPic (Curves.picZeroOfPoint W₁ P) +
            pushPic (Curves.picZeroOfPoint W₁ Q)) := by rw [pushPic.map_add]
    _ = sb2 (pushPic (Curves.picZeroOfPoint W₁ P)) +
        sb2 (pushPic (Curves.picZeroOfPoint W₁ Q)) := by rw [sb2.map_add]
    _ = sb2 (Curves.picZeroOfPoint W₂ (φ.toPointMap cd P)) +
        sb2 (Curves.picZeroOfPoint W₂ (φ.toPointMap cd Q)) := by
          rw [← h_diag, ← h_diag]
    _ = φ.toPointMap cd P + φ.toPointMap cd Q := by
          rw [h_easy_W₂, h_easy_W₂]
