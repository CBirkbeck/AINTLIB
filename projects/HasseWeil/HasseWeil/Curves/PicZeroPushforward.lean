import HasseWeil.Curves.PicZero
import HasseWeil.EC.IsogenyAG

/-!
# Pushforward of (projective) divisors via an isogeny

For an `Isogeny W₁ W₂` with a coordinate-ring witness, this file builds
the divisor-level pushforward `φ_∗ : ProjectiveDivisor (⟨W₁⟩) → ProjectiveDivisor (⟨W₂⟩)`
sending `Σ nᵢ (Pᵢ)` to `Σ nᵢ (φ(Pᵢ))`. This is the basic functoriality
required for the Pic⁰ route to Silverman III.4.8 (Phase C of the
ticket roadmap in `.mathlib-quality/tickets/picard/`).

## Main definitions

* `HasseWeil.EC.Isogeny.pushforwardProjectiveDivisor` — divisor
  pushforward (as an `AddMonoidHom`).

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.3.7 (referenced
  from III.4.8) — pushforward via finite morphisms.
-/

open WeierstrassCurve

namespace HasseWeil.EC.Isogeny

variable {F : Type*} [Field F] [DecidableEq F]
  {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- The pushforward of a projective divisor via an isogeny + coord-ring
witness. Sends `Σ nᵢ (Pᵢ)` to `Σ nᵢ (φ(Pᵢ))` where the point map is the
underlying `Isogeny.toPointMap`. The point at infinity is sent to the
basepoint, which (re-promoted via `Affine.Point.toProjectiveSmoothPoint`)
becomes `infinity` again — so basepoint-mapping is consistent. -/
noncomputable def pushforwardProjectiveDivisor (φ : Isogeny W₁ W₂)
    (cd : φ.toCurveMap.CoordHom) :
    Curves.ProjectiveDivisor (⟨W₁⟩ : Curves.SmoothPlaneCurve F) →+
      Curves.ProjectiveDivisor (⟨W₂⟩ : Curves.SmoothPlaneCurve F) :=
  Finsupp.mapDomain.addMonoidHom fun P =>
    (φ.toPointMap cd P.toAffinePoint).toProjectiveSmoothPoint

@[simp] theorem pushforwardProjectiveDivisor_apply (φ : Isogeny W₁ W₂)
    (cd : φ.toCurveMap.CoordHom)
    (D : Curves.ProjectiveDivisor (⟨W₁⟩ : Curves.SmoothPlaneCurve F)) :
    pushforwardProjectiveDivisor φ cd D =
      Finsupp.mapDomain (fun P =>
        (φ.toPointMap cd P.toAffinePoint).toProjectiveSmoothPoint) D := rfl

@[simp] theorem pushforwardProjectiveDivisor_zero (φ : Isogeny W₁ W₂)
    (cd : φ.toCurveMap.CoordHom) :
    pushforwardProjectiveDivisor φ cd 0 = 0 :=
  (pushforwardProjectiveDivisor φ cd).map_zero

@[simp] theorem pushforwardProjectiveDivisor_add (φ : Isogeny W₁ W₂)
    (cd : φ.toCurveMap.CoordHom) (D₁ D₂) :
    pushforwardProjectiveDivisor φ cd (D₁ + D₂) =
      pushforwardProjectiveDivisor φ cd D₁ +
        pushforwardProjectiveDivisor φ cd D₂ :=
  (pushforwardProjectiveDivisor φ cd).map_add D₁ D₂

@[simp] theorem pushforwardProjectiveDivisor_single (φ : Isogeny W₁ W₂)
    (cd : φ.toCurveMap.CoordHom)
    (P : Curves.ProjectiveSmoothPoint (⟨W₁⟩ : Curves.SmoothPlaneCurve F))
    (n : ℤ) :
    pushforwardProjectiveDivisor φ cd (Finsupp.single P n) =
      Finsupp.single
        ((φ.toPointMap cd P.toAffinePoint).toProjectiveSmoothPoint) n := by
  rw [pushforwardProjectiveDivisor_apply]
  exact Finsupp.mapDomain_single

/-! ### Pushforward preserves degree (T-PIC-C-002) -/

/-- The pushforward preserves the degree of a projective divisor. The
sum of multiplicities is invariant under reindexing the support. -/
theorem degree_pushforwardProjectiveDivisor (φ : Isogeny W₁ W₂)
    (cd : φ.toCurveMap.CoordHom)
    (D : Curves.ProjectiveDivisor (⟨W₁⟩ : Curves.SmoothPlaneCurve F)) :
    Curves.ProjectiveDivisor.degree (pushforwardProjectiveDivisor φ cd D) =
      Curves.ProjectiveDivisor.degree D := by
  rw [pushforwardProjectiveDivisor_apply]
  unfold Curves.ProjectiveDivisor.degree
  rw [Finsupp.sum_mapDomain_index (h := fun _ n => n)
    (fun _ => rfl) (fun _ _ _ => rfl)]

/-- The pushforward restricts to a homomorphism on the degree-zero
subgroup `Div⁰`. -/
noncomputable def pushforwardDegZero (φ : Isogeny W₁ W₂)
    (cd : φ.toCurveMap.CoordHom) :
    Curves.ProjectiveDivisor.degZero (⟨W₁⟩ : Curves.SmoothPlaneCurve F) →+
      Curves.ProjectiveDivisor.degZero (⟨W₂⟩ : Curves.SmoothPlaneCurve F) where
  toFun D :=
    ⟨pushforwardProjectiveDivisor φ cd D.val,
      Curves.ProjectiveDivisor.mem_degZero.mpr <| by
        rw [degree_pushforwardProjectiveDivisor]
        exact Curves.ProjectiveDivisor.mem_degZero.mp D.property⟩
  map_zero' := by
    apply Subtype.ext
    show pushforwardProjectiveDivisor φ cd 0 = 0
    exact (pushforwardProjectiveDivisor φ cd).map_zero
  map_add' D₁ D₂ := by
    apply Subtype.ext
    show pushforwardProjectiveDivisor φ cd (D₁.val + D₂.val) =
      pushforwardProjectiveDivisor φ cd D₁.val +
        pushforwardProjectiveDivisor φ cd D₂.val
    exact (pushforwardProjectiveDivisor φ cd).map_add _ _

/-! ### Divisor-level diagram commute (precursor to T-PIC-D-001)

The Pic⁰-level diagram commute (T-PIC-D-001) needs `pushforwardPicZero`
(T-PIC-C-004), which in turn needs T-PIC-C-003 (preserves principal).
The divisor-level statement below is provable now and slots cleanly into
T-PIC-D-001 once C-003/C-004 land. -/

/-- Divisor-level diagram commute: pushing the `(P) − (O)` divisor of `κ P`
through `φ` gives the `(φ(P)) − (O)` divisor of `κ (φ(P))`. The basepoint
preservation `φ(O) = O` of the isogeny is encoded by
`Isogeny.toPointMap_zero`, which makes the `infinity` term land back at
`infinity`. -/
theorem pushforwardProjectiveDivisor_kappaDivisor (φ : Isogeny W₁ W₂)
    (cd : φ.toCurveMap.CoordHom) (P : W₁.Point) :
    pushforwardProjectiveDivisor φ cd (Curves.kappaDivisor W₁ P) =
      Curves.kappaDivisor W₂ (φ.toPointMap cd P) := by
  have h_zero : φ.toPointMap cd (0 : W₁.Point) = (0 : W₂.Point) :=
    Isogeny.toPointMap_zero φ cd
  unfold Curves.kappaDivisor
  simp only [map_sub, pushforwardProjectiveDivisor_single,
    Affine.Point.toProjectiveSmoothPoint_toAffinePoint,
    Curves.ProjectiveSmoothPoint.toAffinePoint_infinity, h_zero,
    Affine.Point.toProjectiveSmoothPoint_zero]

end HasseWeil.EC.Isogeny
