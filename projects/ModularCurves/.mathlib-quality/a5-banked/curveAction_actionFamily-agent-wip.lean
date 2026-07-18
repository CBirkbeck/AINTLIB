import ModularCurves.Moduli.EngineDescent
open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve
open scoped Pointwise
universe u
namespace ModularCurves.RouteA
variable {G : Type u} [Group G] {X : Scheme.{u}} {C : EllipticCurveGeom X}
  {σ : SchemeAction G X} {σE : SchemeAction G C.E}

theorem curveAction_actionFamily [Finite G]
    (hact : IsCurveAction σ C σE) {Ũ : X.Opens} (hŨs : σ.IsStableOpen Ũ) (hŨa : IsAffineOpen Ũ)
    (W₀ : WeierstrassCurve Γ(X, Ũ)) (e : pullback C.π Ũ.ι ≅ projModel W₀)
    (heπ : e.hom ≫ projModelπ W₀ = pullback.snd C.π Ũ.ι ≫ hŨa.isoSpec.hom)
    (hez : (hŨa.isoSpec.inv ≫ pullback.lift (Ũ.ι ≫ C.zero) (𝟙 _)
        (by rw [Category.assoc, C.zero_π, Category.comp_id, Category.id_comp])) ≫ e.hom
      = projModelZero W₀) :
    letI := σ.gammaMulSemiringAction hŨs
    ∃ act : G → (projModel W₀ ⟶ projModel W₀),
      (∀ g h, act (g * h) = act g ≫ act h) ∧
      (∀ g, IsPullback (act g) (projModelπ W₀) (projModelπ W₀)
        (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G _ g)))) ∧
      (∀ g, projModelZero W₀ ≫ act g
        = Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G _ g)) ≫ projModelZero W₀) := by
  letI := σ.gammaMulSemiringAction hŨs
  refine ⟨fun g => ((σ.pullbackChartAction σE hact.π_equivariant hŨs).transport e).hom g,
    fun g h => ((σ.pullbackChartAction σE hact.π_equivariant hŨs).transport e).hom_mul g h, ?_, ?_⟩
  · intro g; sorry
  · intro g; sorry
