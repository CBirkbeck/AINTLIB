import ModularCurves.EllipticCurve.TorsionFibre
import ModularCurves.ForMathlib.FormallyUnramifiedFibre
import ModularCurves.ForMathlib.NilpotentKerSpecMap
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# L-BC: `E[N] ⟶ S` is formally unramified when `N` is invertible (BB-DIFF, the fibre leg)

The [T-B6′]-fill session's `hfib` discharge (CHARTER-Y1-CLOSER S2; board v10.123/124-CASCADE):
the residue-field fibres of `E.torsionπ N` are formally unramified, hence — through the
pre-wired T-DISC funnel — so is `E[N] ⟶ S` itself.

**The fibre-level core is the augmentation-ideal rigidity of torsion** (KM 2.3.1 p. 74, in
infinitesimal form; no invariant differentials, no degree counts): over a field `k`, a point
`D` of `E` that (i) reduces to the zero section along a square-zero thickening `R ↠ R/I` and
(ii) is killed by an `N` invertible in `k`, is the zero point. Route: `D` factors through an
affine chart `U ∋ e` and its comorphism sends the augmentation ideal `J = ker (ε : Γ(U) → k)`
into `I`; on such points, evaluation at `J` is *additive* — the co-multiplication satisfies
`μ♯ f ≡ f ⊗ 1 + 1 ⊗ f mod J ⊗ J` (the counit laws), and `J ⊗ J`-terms die in `I² = 0` — so
`N • D = 0` forces `N · D♯(f) = 0`, and `N ∈ k˟` forces `D♯(J) = 0`, i.e. `D` *is* the zero
section. This gives `formallyUnramified_torsionπ_of_isUnit` over every field via
`FormallyUnramified.of_hom_ext`, and `formallyUnramified_torsionπ_of_nIsInvertible` (= L-BC)
over every base via `FormallyUnramified.of_finite_fiberToSpecResidueField` (T-DISC) +
`torsion_baseChange_isPullback`.

The three `Point`-restriction lemmas at the head are relocated byte-identically from
`MulByHomUnramified.lean` (which now imports this file; pointer comments at the old site) —
they are needed on both sides of the L-A/L-BC split.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- `pointEquivOverHom` carries point-subtraction to the division of `Over`-homs (companion to
`pointEquivOverHom_add`). -/
theorem pointEquivOverHom_sub {T : Scheme.{u}} (g : T ⟶ S) (P Q : E.Point g) :
    letI : CommGroup (Over.mk g ⟶ E.asOver) := Hom.commGroup
    (E.pointEquivOverHom g) (P - Q) =
      (E.pointEquivOverHom g) P / (E.pointEquivOverHom g) Q := rfl

/-- Restriction of a point along `k` corresponds, under `pointEquivOverHom`, to precomposition by
the induced `Over`-morphism `Over.mk (k ≫ g) ⟶ Over.mk g`. -/
theorem pointEquivOverHom_restrict {T T' : Scheme.{u}} {g : T ⟶ S} (k : T' ⟶ T) (P : E.Point g) :
    E.pointEquivOverHom (k ≫ g) (Point.restrict E k P) =
      (Over.homMk k : Over.mk (k ≫ g) ⟶ Over.mk g) ≫ E.pointEquivOverHom g P := by
  apply Over.OverMorphism.ext
  simp only [pointEquivOverHom, Equiv.coe_fn_mk, Point.restrict, Over.comp_left, Over.homMk_left]
  rfl

/-- `Point.restrict` is additive on subtraction (precomposition is a group homomorphism). -/
theorem restrict_sub {T T' : Scheme.{u}} {g : T ⟶ S} (k : T' ⟶ T) (P Q : E.Point g) :
    Point.restrict E k (P - Q) = Point.restrict E k P - Point.restrict E k Q := by
  apply (E.pointEquivOverHom (k ≫ g)).injective
  simp only [E.pointEquivOverHom_restrict, E.pointEquivOverHom_sub, GrpObj.comp_div]

/-- **(L-BC core: augmentation-ideal rigidity of torsion)** Over a field `k`, a point of `E`
over `Spec R` that reduces to the zero point along a square-zero quotient `φ : R ↠ S'` and is
killed by an `N` invertible in `k` is the zero point. This is the infinitesimal-fibre content
of KM 2.3.1 ("its tangent map at the origin being multiplication by N"), proven without
differentials: the kernel of reduction is `N`-torsion-free because evaluation on the
augmentation ideal of a chart at the zero section is additive modulo `I² = 0`. -/
theorem point_eq_zero_of_smul_eq_zero_of_restrict_eq_zero
    {k : CommRingCat.{u}} [Field k] (F : EllipticCurve (Spec k))
    {R S' : CommRingCat.{u}} (φ : R ⟶ S') (hφ : Function.Surjective φ.hom)
    (hφ2 : RingHom.ker φ.hom ^ 2 = ⊥)
    {t : Spec R ⟶ Spec k} (D : F.Point t)
    (hres : Point.restrict F (Spec.map φ) D = 0)
    (N : ℕ) (hN : IsUnit (N : k)) (hND : (N : ℤ) • D = 0) :
    D = 0 := by
  sorry

/-- **(L-B, field case)** Over a field in which `N` is invertible, the `N`-torsion
`E[N] ⟶ Spec k` is formally unramified: lifts along square-zero thickenings are unique,
because the difference of two lifts is an `N`-torsion point of `E` reducing to zero
(`point_eq_zero_of_smul_eq_zero_of_restrict_eq_zero`). -/
theorem formallyUnramified_torsionπ_of_isUnit
    {k : CommRingCat.{u}} [Field k] (F : EllipticCurve (Spec k))
    (N : ℕ) (hN : IsUnit (N : k)) :
    FormallyUnramified (F.torsionπ N) := by
  apply FormallyUnramified.of_hom_ext
  intro R S' φ hφ hφ2 g₁ g₂ hthick hf
  set t : Spec R ⟶ Spec k := g₁ ≫ F.torsionπ N with ht
  have ht₂ : g₂ ≫ F.torsionπ N = t := hf.symm
  -- the two lifts as `N`-torsion points of `E`
  set T₁ := F.torsionPointsEquiv N t ⟨g₁, rfl⟩ with hT₁
  set T₂ := F.torsionPointsEquiv N t ⟨g₂, ht₂⟩ with hT₂
  -- their difference is `N`-torsion and reduces to zero
  have hND : (N : ℤ) • ((T₁ : F.Point t) - (T₂ : F.Point t)) = 0 := by
    rw [smul_sub, (Submodule.mem_torsionBy_iff _ _).mp T₁.2,
      (Submodule.mem_torsionBy_iff _ _).mp T₂.2, sub_zero]
  have hresD : Point.restrict F (Spec.map φ) ((T₁ : F.Point t) - (T₂ : F.Point t)) = 0 := by
    rw [F.restrict_sub]
    have hPeq : Point.restrict F (Spec.map φ) (T₁ : F.Point t) =
        Point.restrict F (Spec.map φ) (T₂ : F.Point t) := by
      refine Subtype.ext ?_
      show Spec.map φ ≫ (g₁ ≫ F.torsionι N) = Spec.map φ ≫ (g₂ ≫ F.torsionι N)
      rw [← Category.assoc, ← Category.assoc, hthick]
    rw [hPeq, sub_self]
  -- the core kills the difference
  have hD0 : (T₁ : F.Point t) - (T₂ : F.Point t) = 0 :=
    point_eq_zero_of_smul_eq_zero_of_restrict_eq_zero F φ hφ hφ2 _ hresD N hN hND
  have hT : T₁ = T₂ := Subtype.ext (sub_eq_zero.mp hD0)
  have := congrArg (fun z => ((F.torsionPointsEquiv N t).symm z).1) hT
  simpa [hT₁, hT₂, Equiv.symm_apply_apply] using this

/-- `N` invertible on `S` is `N` invertible in every residue field of `S`. -/
theorem nIsInvertible_residueField {X : Scheme.{u}} {N : ℕ} (h : NIsInvertible X N) (x : X) :
    IsUnit (N : X.residueField x) := by
  have h0 : IsUnit ((N : ℕ) : Γ(X, ⊤)) := h
  have h1 := (X.presheaf.germ ⊤ x trivial ≫ X.residue x).hom.isUnit_map h0
  rwa [map_natCast] at h1

/-- **(L-BC = `formallyUnramified_torsionπ`, the arithmetic input of BB-DIFF)** If `N` is
invertible on `S`, the `N`-torsion `E[N] ⟶ S` is formally unramified: by T-DISC
(`FormallyUnramified.of_finite_fiberToSpecResidueField`, using `torsionπ_isFinite`) it
suffices that every residue-field fibre is formally unramified; the fibre at `y` is the
torsion of the base change to `Spec κ(y)` (`torsion_baseChange_isPullback`), which is
formally unramified by the field case. -/
theorem formallyUnramified_torsionπ_of_nIsInvertible (N : ℕ) (h : NIsInvertible S N) :
    FormallyUnramified (E.torsionπ N) := by
  rcases eq_or_ne N 0 with rfl | hN0
  · haveI hS : IsEmpty S := ModularCurves.isEmpty_of_nIsInvertible_zero h
    haveI hT : IsEmpty (E.torsion 0) := ⟨fun x => hS.false ((E.torsionπ 0).base x)⟩
    infer_instance
  · haveI : NeZero N := ⟨hN0⟩
    haveI := E.torsionπ_isFinite N
    apply FormallyUnramified.of_finite_fiberToSpecResidueField
    intro y
    -- the base-changed torsion over the residue field is formally unramified
    have hbc : FormallyUnramified ((E.baseChange (S.fromSpecResidueField y)).torsionπ N) :=
      formallyUnramified_torsionπ_of_isUnit
        (E.baseChange (S.fromSpecResidueField y)) N (nIsInvertible_residueField h y)
    -- both are pullbacks of `torsionπ` along `Spec κ(y) ⟶ S`: transfer across the iso
    have h1 : IsPullback (E.torsionBaseChangeHom N (S.fromSpecResidueField y))
        ((E.baseChange (S.fromSpecResidueField y)).torsionπ N)
        (E.torsionπ N) (S.fromSpecResidueField y) :=
      E.torsion_baseChange_isPullback N (S.fromSpecResidueField y)
    have h2 : IsPullback ((E.torsionπ N).fiberι y) ((E.torsionπ N).fiberToSpecResidueField y)
        (E.torsionπ N) (S.fromSpecResidueField y) :=
      IsPullback.of_hasPullback (E.torsionπ N) (S.fromSpecResidueField y)
    rw [← h2.isoIsPullback_hom_snd _ _ h1,
      MorphismProperty.cancel_left_of_respectsIso (P := @AlgebraicGeometry.FormallyUnramified)]
    exact hbc

end EllipticCurve

end ModularCurves
