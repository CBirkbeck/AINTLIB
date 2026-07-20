/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.LevelStructure.Factorization
import ModularCurves.EllipticCurve.TorsionFibre
import ModularCurves.ForMathlib.UnramifiedEqualizer

/-!
# The exact-order boxes at invertible `N` (T-E4F1 / T-E4F2)

The invertible-`N` instances of the two `LevelStructure/ExactOrder.lean` register boxes,
proven WITHOUT the over-`ℤ` Oort–Tate/Deligne black box:

* `RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors_of_invertible` — **KM 1.4.2 at
  invertible `N`**: a degree-`N` subgroup divisor kills every point factoring through it,
  provided `N` is invertible on the base.  This is the invertible-`N` shadow of the
  general-base box `smul_eq_zero_of_factors` (`ExactOrder.lean`, statement-protected).
* `Section.HasExactOrder.smul_eq_zero_of_invertible` — KM 1.4.2 for `orderDivisor`.
* `Section.HasExactOrder.pull_nsmul_ne_zero_of_invertible` — **KM 1.4.4 (1)⟹(3)**: at a
  geometric point the proper multiples of an exact-order-`N` point are nonzero; the
  invertible-`N` bypass of the char-`p` jet keystone `pull_nsmul_jetData`
  (`ExactOrder.lean:832`, statement-protected).

## The route (no Oort–Tate, no fat-point jets)

1. **Universal point** (KM p. 27's trick, `DeligneOrder`-style): the box for every
   `T`-point reduces to killing the single universal point `upt : D.subscheme ⟶ E`
   (`smul_eq_zero_of_factors_of_upt`).
2. **Affine convolution dictionary**: over an affine base `Spec R` the factoring of
   `n • upt` through `D` is an endomorphism `wₙ` of the (affine) divisor scheme, and
   `Γ(wₙ) = (toConv id)^n` — the `n`-th CONVOLUTION power of the identity in the
   convolution algebra `WithConv (A →ₗ[R] A)` dual to the subgroup Hopf algebra
   `A = Γ(D.subscheme)` (`GroupScheme/DeligneOrder`, proven Layer-B Hopf package).
3. **Abstract Deligne over a field** (`ForMathlib/CartierDual`, proven Layer A —
   Tate §3.8): `A` is finite FREE over a field, so `(toConv id)^N = 1`, whence
   `N • upt = 0` — the box over ANY field base (`smul_eq_zero_of_factors_of_field`).
4. **Spread to invertible `N`** (KM 1.4.4(4)-style): fibrewise, the killed universal
   point puts the fibre divisor inside the finite étale `E[N]` (`torsionπ` unramified at
   invertible `N`), so `D.subscheme ⟶ S` has formally unramified fibres, hence is
   unramified (`ForMathlib/FormallyUnramifiedFibre`); the two factorings of `N • upt`
   and `0` then agree at every (residue-field) point by step 3, hence globally by the
   clopen-equalizer detection engine (`ForMathlib/UnramifiedEqualizer`).
5. **Distinctness of multiples** (KM 1.4.4(3), T-E4F2): over `k̄` the divisor scheme of
   an exact-order-`N` point is finite étale of rank `N` (steps 3–4 make it a closed
   subscheme of the étale `E[N]`), so it has exactly `N` sections
   (`natCard_sections_eq_finrank`); the exhaustion engine
   (`point_eq_section_of_factors`, KM p. 29) pins every section as a multiple `aP`, and
   a proper relation `a • P = 0` would leave fewer than `N` multiples — contradiction.
-/

open AlgebraicGeometry CategoryTheory Limits Coalgebra WithConv
open scoped TensorProduct

universe u

namespace ModularCurves

namespace EllipticCurve

section UniversalPoint

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- Every integer multiple of the universal point of a subgroup divisor factors through
the divisor (KM p. 27's universal-point trick, `zsmul` form of
`RelEffCartierDiv.IsSubgroup.exists_smul_restrict`). -/
theorem _root_.ModularCurves.RelEffCartierDiv.IsSubgroup.exists_zsmul_upt_factor
    {D : RelEffCartierDiv E.π} (hD : D.IsSubgroup E) (c : ℤ) :
    ∃ w : D.ideal.subscheme ⟶ D.ideal.subscheme,
      w ≫ D.ideal.subschemeι = (c • E.upt (D := D)).1 := by
  obtain ⟨H, hH⟩ := hD (D.ideal.subschemeι ≫ E.π)
  exact (hH _).mp (AddSubgroup.zsmul_mem H
    ((hH (E.upt (D := D))).mpr ⟨𝟙 _, Category.id_comp _⟩) c)

/-- **The universal-point reduction**: if the universal point of a subgroup divisor is
killed by `N`, then so is every point factoring through the divisor, over every `T`. -/
theorem _root_.ModularCurves.RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors_of_upt
    {D : RelEffCartierDiv E.π} {N : ℕ}
    (hupt : (N : ℤ) • E.upt (D := D) = 0) {T : Scheme.{u}} (g : T ⟶ S) (Q : E.Point g)
    (hQ : ∃ h : T ⟶ D.ideal.subscheme, h ≫ D.ideal.subschemeι = Q.1) :
    (N : ℤ) • Q = 0 := by
  obtain ⟨w, hw⟩ := hQ
  refine Subtype.ext ?_
  have h1 : ((N : ℤ) • Q).1 = Q.1 ≫ E.mulByHom (N : ℤ) :=
    E.point_smul_eq_comp_mulBy g (N : ℤ) Q
  have h2 : (((N : ℤ) • E.upt (D := D)).1 : D.ideal.subscheme ⟶ E.E)
      = D.ideal.subschemeι ≫ E.mulByHom (N : ℤ) :=
    E.point_smul_eq_comp_mulBy _ (N : ℤ) (E.upt (D := D))
  have h3 : (((N : ℤ) • E.upt (D := D)).1 : D.ideal.subscheme ⟶ E.E)
      = (D.ideal.subschemeι ≫ E.π) ≫ E.zero := by
    rw [hupt]
    exact E.point_zero_val _
  calc ((N : ℤ) • Q).1 = Q.1 ≫ E.mulByHom (N : ℤ) := h1
    _ = (w ≫ D.ideal.subschemeι) ≫ E.mulByHom (N : ℤ) := by rw [hw]
    _ = w ≫ (D.ideal.subschemeι ≫ E.mulByHom (N : ℤ)) := Category.assoc _ _ _
    _ = w ≫ ((D.ideal.subschemeι ≫ E.π) ≫ E.zero) := by rw [← h2, h3]
    _ = ((w ≫ D.ideal.subschemeι) ≫ E.π) ≫ E.zero := by
        simp only [Category.assoc]
    _ = (Q.1 ≫ E.π) ≫ E.zero := by rw [hw]
    _ = g ≫ E.zero := by rw [Q.2]
    _ = ((0 : E.Point g).1 : T ⟶ E.E) := (E.point_zero_val g).symm

end UniversalPoint

section AffineConv

/-! ### The Γ-convolution dictionary over an affine base

Over `S = Spec R`, the factoring `wₙ : D.subscheme ⟶ D.subscheme` of the `n`-th multiple
of the universal point through the subgroup divisor has `Γ(wₙ) = (toConv id)^n`, the
`n`-th convolution power of the identity in `WithConv (A →ₗ[R] A)` — dual to the
subgroup coalgebra of `GroupScheme/DeligneOrder`. -/

variable {R : Type u} [CommRing R] (E : EllipticCurve (Spec (CommRingCat.of R)))
  (D : RelEffCartierDiv E.π)

/-- Morphisms between the (affine) divisor scheme are determined by their global-section
rings: `Spec`-Γ faithfulness through `isoSpec`. -/
private theorem subgroupHom_ext (w w' : D.ideal.subscheme ⟶ D.ideal.subscheme)
    (h : w.appTop = w'.appTop) : w = w' := by
  haveI : IsFinite (E.subgroupStructMap D) := D.finite
  haveI : IsAffine D.ideal.subscheme := isAffine_of_isAffineHom (E.subgroupStructMap D)
  have h1 := Scheme.isoSpec_hom_naturality w
  have h2 := Scheme.isoSpec_hom_naturality w'
  rw [h] at h1
  have := h1.symm.trans h2
  exact (cancel_mono (D.ideal.subscheme.isoSpec.hom)).mp this

/-- The canonical zero factoring `q ≫ e` of the zero point through the divisor, on global
sections: `Γ(q ≫ e) = algebraMap ∘ ε` (`ε = subgroupCounit`). -/
private theorem appTop_structMap_subgroupUnit (hD : D.IsSubgroup E)
    (a : Γ(D.ideal.subscheme, ⊤)) :
    letI := E.subgroupAlgebra D
    (E.subgroupStructMap D ≫ E.subgroupUnit hD).appTop.hom a
      = algebraMap R Γ(D.ideal.subscheme, ⊤) (E.subgroupCounit hD a) := by
  letI := E.subgroupAlgebra D
  have hcomp : (E.subgroupStructMap D ≫ E.subgroupUnit hD).appTop
      = (E.subgroupUnit hD).appTop ≫ (E.subgroupStructMap D).appTop :=
    Scheme.Hom.comp_appTop _ _
  have h1 : (E.subgroupStructMap D ≫ E.subgroupUnit hD).appTop.hom a
      = (E.subgroupStructMap D).appTop.hom ((E.subgroupUnit hD).appTop.hom a) := by
    rw [hcomp]
    exact CommRingCat.comp_apply _ _ a
  rw [h1]
  -- RHS: `algebraMap = (ΓSpecIso.inv ≫ q.appTop).hom`, `ε a = (e.appTop ≫ ΓSpecIso.hom).hom a`
  show (E.subgroupStructMap D).appTop.hom ((E.subgroupUnit hD).appTop.hom a)
      = ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop).hom
          (((E.subgroupUnit hD).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom a)
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply]
  congr 1
  have hcancel := congrArg
    (fun f : Γ(Spec (CommRingCat.of R), ⊤) ⟶ Γ(Spec (CommRingCat.of R), ⊤) =>
      f.hom ((E.subgroupUnit hD).appTop.hom a))
    (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of R)))
  simp only [CommRingCat.comp_apply] at hcancel
  rw [hcancel]
  simp

set_option maxRecDepth 4000 in
/-- **The Γ-convolution dictionary** (the heart of the invertible-`N` box): any factoring
`w` of `n • upt` through the subgroup divisor over an affine base has
`Γ(w) = (toConv id)^n` in the convolution algebra `WithConv (A →ₗ[R] A)` of the subgroup
coalgebra. Induction on `n`; the step is the dualization `Γ(m) = κ ∘ Δ` of the group law
(`subgroupTensorCompare_subgroupComul`) evaluated through a Sweedler representative. -/
private theorem appTop_eq_convPow_of_factor (hD : D.IsSubgroup E) :
    letI := E.subgroupAlgebra D
    letI := E.subgroupCoalgebra hD
    ∀ (n : ℕ) (w : D.ideal.subscheme ⟶ D.ideal.subscheme),
      w ≫ D.ideal.subschemeι = (((n : ℤ)) • E.upt (D := D)).1 →
      ∀ a : Γ(D.ideal.subscheme, ⊤),
        w.appTop.hom a
          = ((toConv (LinearMap.id : Γ(D.ideal.subscheme, ⊤) →ₗ[R]
              Γ(D.ideal.subscheme, ⊤)) ^ n :
              WithConv (Γ(D.ideal.subscheme, ⊤) →ₗ[R] Γ(D.ideal.subscheme, ⊤)))) a := by
  letI := E.subgroupAlgebra D
  letI := E.subgroupCoalgebra hD
  intro n
  induction n with
  | zero =>
    intro w hw a
    -- `w` is the canonical zero factoring `q ≫ e`
    have hze : (E.subgroupStructMap D ≫ E.subgroupUnit hD) ≫ D.ideal.subschemeι
        = (((0 : ℕ) : ℤ) • E.upt (D := D)).1 := by
      rw [Nat.cast_zero, zero_zsmul, Category.assoc, E.subgroupUnit_subschemeι hD]
      show E.subgroupStructMap D ≫ (0 : E.Point (𝟙 (Spec (CommRingCat.of R)))).1
          = (0 : E.Point (D.ideal.subschemeι ≫ E.π)).1
      rw [E.point_zero_val, E.point_zero_val, Category.id_comp]
    have hwz : w = E.subgroupStructMap D ≫ E.subgroupUnit hD :=
      (cancel_mono D.ideal.subschemeι).mp (hw.trans hze.symm)
    rw [hwz]
    -- RHS: `(toConv id)^0 = 1`, and `1 a = algebraMap (counit a)`
    refine (appTop_structMap_subgroupUnit E D hD a).trans ?_
    rw [pow_zero]
    exact (LinearMap.convOne_apply a).symm
  | succ n ih =>
    intro w hw a
    -- the previous factoring
    obtain ⟨wn, hwn⟩ := RelEffCartierDiv.IsSubgroup.exists_zsmul_upt_factor E hD (n : ℤ)
    have hwnq : wn ≫ E.subgroupStructMap D = E.subgroupStructMap D := by
      show wn ≫ D.ideal.subschemeι ≫ E.π = D.ideal.subschemeι ≫ E.π
      rw [← Category.assoc, hwn]
      exact (((n : ℤ)) • E.upt (D := D)).2
    -- the pairing morphism into `D ×_R D`
    set pl : D.ideal.subscheme ⟶
        pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π) :=
      pullback.lift wn (𝟙 _) (by
        rw [Category.id_comp]
        exact hwnq) with hpl
    have hplfst : pl ≫ pullback.fst _ _ = wn := pullback.lift_fst _ _ _
    have hplsnd : pl ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have hbase : pl ≫ E.bimulBase (D := D) = D.ideal.subschemeι ≫ E.π := by
      show pl ≫ pullback.fst _ _ ≫ D.ideal.subschemeι ≫ E.π = _
      rw [← Category.assoc, hplfst]
      exact hwnq
    -- the universal point transported to the `pl`-base
    set upt' : E.Point (pl ≫ E.bimulBase (D := D)) :=
      ⟨D.ideal.subschemeι, by rw [hbase]⟩ with hupt'
    have hA1 : Point.restrict E pl (E.bipt₁ (D := D)) = ((n : ℤ)) • upt' := by
      refine Subtype.ext ?_
      have hval : (Point.restrict E pl (E.bipt₁ (D := D))).1
          = pl ≫ pullback.fst _ _ ≫ D.ideal.subschemeι := rfl
      rw [hval, ← Category.assoc, hplfst, hwn,
        E.point_smul_eq_comp_mulBy _ ((n : ℤ)) (E.upt (D := D)),
        E.point_smul_eq_comp_mulBy _ ((n : ℤ)) upt']
      rfl
    have hA2 : Point.restrict E pl (E.bipt₂ (D := D)) = upt' := by
      refine Subtype.ext ?_
      have hval : (Point.restrict E pl (E.bipt₂ (D := D))).1
          = pl ≫ pullback.snd _ _ ≫ D.ideal.subschemeι := rfl
      rw [hval, ← Category.assoc, hplsnd, Category.id_comp]
    -- the composed factoring equals `w`
    have hcomp : (pl ≫ E.subgroupMul hD) ≫ D.ideal.subschemeι
        = (((n + 1 : ℕ) : ℤ) • E.upt (D := D)).1 := by
      rw [Category.assoc, E.subgroupMul_subschemeι hD]
      have hkey : pl ≫ ((E.bipt₁ (D := D)) + (E.bipt₂ (D := D))).1
          = (Point.restrict E pl ((E.bipt₁ (D := D)) + (E.bipt₂ (D := D)))).1 := rfl
      rw [hkey, Point.restrict_add, hA1, hA2]
      have hsum : ((n : ℤ)) • upt' + upt' = ((n + 1 : ℕ) : ℤ) • upt' := by
        have : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
        rw [this, add_zsmul, one_zsmul]
      rw [hsum, E.point_smul_eq_comp_mulBy _ (((n + 1 : ℕ) : ℤ)) upt',
        E.point_smul_eq_comp_mulBy _ (((n + 1 : ℕ) : ℤ)) (E.upt (D := D))]
      rfl
    have hwcomp : w = pl ≫ E.subgroupMul hD :=
      (cancel_mono D.ideal.subschemeι).mp (hw.trans hcomp.symm)
    -- Γ of the composition
    have hΓcomp : w.appTop.hom a
        = pl.appTop.hom ((E.subgroupMul hD).appTop.hom a) := by
      rw [hwcomp]
      have : (pl ≫ E.subgroupMul hD).appTop
          = (E.subgroupMul hD).appTop ≫ pl.appTop := Scheme.Hom.comp_appTop _ _
      rw [this]
      exact CommRingCat.comp_apply _ _ a
    rw [hΓcomp]
    -- `Γ(m) a = κ (Δ a)` and expand `Δ a` through a Sweedler representative
    have hκΔ : (E.subgroupMul hD).appTop.hom a
        = E.subgroupTensorCompare (D := D) (E.subgroupComul hD a) := by
      exact (E.subgroupTensorCompare_subgroupComul hD a).symm
    rw [hκΔ]
    have hΔ : E.subgroupComul hD a
        = ∑ i ∈ (ℛ R a).index, (ℛ R a).left i ⊗ₜ[R] (ℛ R a).right i :=
      ((ℛ R a).eq).symm
    rw [hΔ, map_sum, map_sum]
    -- per-term computation
    have hterm : ∀ i ∈ (ℛ R a).index,
        pl.appTop.hom (E.subgroupTensorCompare (D := D)
            ((ℛ R a).left i ⊗ₜ[R] (ℛ R a).right i))
          = ((toConv (LinearMap.id : Γ(D.ideal.subscheme, ⊤) →ₗ[R]
              Γ(D.ideal.subscheme, ⊤)) ^ n :
              WithConv (Γ(D.ideal.subscheme, ⊤) →ₗ[R] Γ(D.ideal.subscheme, ⊤))))
                ((ℛ R a).left i) * (ℛ R a).right i := by
      intro i _
      rw [E.subgroupTensorCompare_tmul hD ((ℛ R a).left i) ((ℛ R a).right i), map_mul]
      congr 1
      · -- first factor: `Γ(pl)(Γ(fst) x) = Γ(wn) x = (toConv id)^n x`
        have h1 : pl.appTop.hom (E.subgroupProj₁ (D := D) ((ℛ R a).left i))
            = (pl ≫ pullback.fst (D.ideal.subschemeι ≫ E.π)
                (D.ideal.subschemeι ≫ E.π)).appTop.hom ((ℛ R a).left i) := by
          have : (pl ≫ pullback.fst (D.ideal.subschemeι ≫ E.π)
              (D.ideal.subschemeι ≫ E.π)).appTop
              = (pullback.fst (D.ideal.subschemeι ≫ E.π)
                  (D.ideal.subschemeι ≫ E.π)).appTop ≫ pl.appTop :=
            Scheme.Hom.comp_appTop _ _
          rw [this]
          exact (CommRingCat.comp_apply _ _ _).symm
        rw [h1, hplfst]
        exact ih wn hwn ((ℛ R a).left i)
      · -- second factor: `Γ(pl)(Γ(snd) y) = Γ(𝟙) y = y`
        have h2 : pl.appTop.hom (E.subgroupProj₂ (D := D) ((ℛ R a).right i))
            = (pl ≫ pullback.snd (D.ideal.subschemeι ≫ E.π)
                (D.ideal.subschemeι ≫ E.π)).appTop.hom ((ℛ R a).right i) := by
          have : (pl ≫ pullback.snd (D.ideal.subschemeι ≫ E.π)
              (D.ideal.subschemeι ≫ E.π)).appTop
              = (pullback.snd (D.ideal.subschemeι ≫ E.π)
                  (D.ideal.subschemeι ≫ E.π)).appTop ≫ pl.appTop :=
            Scheme.Hom.comp_appTop _ _
          rw [this]
          exact (CommRingCat.comp_apply _ _ _).symm
        rw [h2, hplsnd]
        simp
    rw [Finset.sum_congr rfl hterm]
    -- RHS: the convolution power at `n+1` through the same representative
    rw [pow_succ, (ℛ R a).convMul_apply]
    exact Finset.sum_congr rfl fun i _ => rfl
end AffineConv

section FieldBox

/-! ### The box over a field base

Over `Spec k` the coordinate ring `A` of the divisor scheme is finite FREE, so the
abstract Deligne theorem (`ForMathlib/CartierDual`) applies to the convolution
dictionary above: `(toConv id)^N = 1`, hence `N • upt = 0` — the full box over any field
base, with NO invertibility hypothesis. -/

variable {k : Type u} [Field k] (E : EllipticCurve (Spec (CommRingCat.of k)))

/-- **KM 1.4.2 over a field, universal-point core**: the universal point of a degree-`N`
subgroup divisor over a field is killed by `N`. Deligne's abstract order theorem
(`deligne_pointConv_pow_finrank`, Tate §3.8 — proven Layer A) applied to the identity
point through the Γ-convolution dictionary (`appTop_eq_convPow_of_factor`). -/
theorem _root_.ModularCurves.RelEffCartierDiv.IsSubgroup.smul_upt_eq_zero_of_field
    {D : RelEffCartierDiv E.π} (hD : D.IsSubgroup E) {N : ℕ} [NeZero N]
    (hdeg : ∀ s, D.degree s = N) :
    (N : ℤ) • E.upt (D := D) = 0 := by
  classical
  letI := E.subgroupAlgebra D
  letI := E.subgroupCoalgebra hD
  letI := E.subgroupHopfAlgebra hD
  haveI := E.subgroupIsCocomm hD
  haveI hfin : Module.Finite k ↑Γ(D.ideal.subscheme, ⊤) := E.subgroupAlgebra_finite D
  haveI : IsFinite (E.subgroupStructMap D) := D.finite
  haveI : IsAffine D.ideal.subscheme := isAffine_of_isAffineHom (E.subgroupStructMap D)
  -- the finrank bridge: `finrank k A = N`
  obtain ⟨s₀⟩ : Nonempty ↑(Spec (CommRingCat.of k)) := inferInstance
  have hdeg₀ : (E.subgroupStructMap D).finrank s₀ = N := hdeg s₀
  have hspec : Spec.map (CommRingCat.ofHom (algebraMap k ↑Γ(D.ideal.subscheme, ⊤)))
      = D.ideal.subscheme.isoSpec.inv ≫ D.ideal.subschemeι ≫ E.π :=
    E.subgroupSpecAlgebraMap_eq (D := D)
  have h1 : (E.subgroupStructMap D).finrank s₀
      = (D.ideal.subscheme.isoSpec.inv ≫ E.subgroupStructMap D).finrank s₀ :=
    (congrFun (Scheme.Hom.finrank_comp_left_of_isIso _ _) s₀).symm
  have h2 : (D.ideal.subscheme.isoSpec.inv ≫ E.subgroupStructMap D).finrank s₀
      = (Spec.map (CommRingCat.ofHom
          (algebraMap k ↑Γ(D.ideal.subscheme, ⊤)))).finrank s₀ := by
    rw [hspec]
  have h3 : (Spec.map (CommRingCat.ofHom
        (algebraMap k ↑Γ(D.ideal.subscheme, ⊤)))).finrank s₀
      = Module.rankAtStalk (R := k) ↑Γ(D.ideal.subscheme, ⊤) s₀ :=
    Scheme.Hom.finrank_SpecMap_algebraMap k ↑Γ(D.ideal.subscheme, ⊤) s₀
  have h4 : Module.rankAtStalk (R := k) ↑Γ(D.ideal.subscheme, ⊤) s₀
      = Module.finrank k ↑Γ(D.ideal.subscheme, ⊤) := by
    rw [Module.rankAtStalk_eq_finrank_of_free]
    rfl
  have hfr : Module.finrank k ↑Γ(D.ideal.subscheme, ⊤) = N := by
    rw [← h4, ← h3, ← h2, ← h1]
    exact hdeg₀
  -- nontriviality of the coordinate ring and of the convolution algebra
  haveI hntA : Nontrivial ↑Γ(D.ideal.subscheme, ⊤) := by
    refine Module.nontrivial_of_finrank_pos (R := k) ?_
    rw [hfr]
    exact Nat.pos_of_ne_zero (NeZero.ne N)
  haveI : Nontrivial (WithConv (↑Γ(D.ideal.subscheme, ⊤) →ₗ[k]
      ↑Γ(D.ideal.subscheme, ⊤))) := by
    refine ⟨1, 0, fun hcon => ?_⟩
    have h1' := congrArg (fun f : WithConv (↑Γ(D.ideal.subscheme, ⊤) →ₗ[k]
        ↑Γ(D.ideal.subscheme, ⊤)) => f (1 : ↑Γ(D.ideal.subscheme, ⊤))) hcon
    simp only [LinearMap.convOne_apply] at h1'
    have hε1 : Coalgebra.counit (R := k) (1 : ↑Γ(D.ideal.subscheme, ⊤)) = 1 :=
      map_one (E.subgroupCounit hD)
    rw [hε1, map_one] at h1'
    exact one_ne_zero h1'
  -- Deligne's abstract theorem at the identity point
  have hdel : (CartierDual.pointConv (AlgHom.id k ↑Γ(D.ideal.subscheme, ⊤)))
      ^ (Module.finrank k ↑Γ(D.ideal.subscheme, ⊤)) = 1 :=
    CartierDual.deligne_pointConv_pow_finrank _
  rw [hfr] at hdel
  have hdel' : (toConv (LinearMap.id : ↑Γ(D.ideal.subscheme, ⊤) →ₗ[k]
      ↑Γ(D.ideal.subscheme, ⊤)) : WithConv _) ^ N = 1 := by
    have : (CartierDual.pointConv (AlgHom.id k ↑Γ(D.ideal.subscheme, ⊤)))
        = toConv (LinearMap.id : ↑Γ(D.ideal.subscheme, ⊤) →ₗ[k]
            ↑Γ(D.ideal.subscheme, ⊤)) := rfl
    rw [← this]
    exact hdel
  -- the `N`-th factoring computes as the zero factoring on global sections
  obtain ⟨w, hw⟩ := RelEffCartierDiv.IsSubgroup.exists_zsmul_upt_factor E hD ((N : ℕ) : ℤ)
  have hΓ : ∀ a : ↑Γ(D.ideal.subscheme, ⊤),
      w.appTop.hom a = (E.subgroupStructMap D ≫ E.subgroupUnit hD).appTop.hom a := by
    intro a
    rw [appTop_eq_convPow_of_factor E D hD N w hw a, hdel',
      appTop_structMap_subgroupUnit E D hD a]
    rfl
  have happ : w.appTop = (E.subgroupStructMap D ≫ E.subgroupUnit hD).appTop := by
    ext a
    exact hΓ a
  have hww : w = E.subgroupStructMap D ≫ E.subgroupUnit hD :=
    subgroupHom_ext E D w _ happ
  -- conclude
  refine Subtype.ext ?_
  have hz : ((E.subgroupStructMap D ≫ E.subgroupUnit hD) ≫ D.ideal.subschemeι :
      D.ideal.subscheme ⟶ E.E)
      = (0 : E.Point (D.ideal.subschemeι ≫ E.π)).1 := by
    rw [Category.assoc, E.subgroupUnit_subschemeι hD]
    show E.subgroupStructMap D ≫ (0 : E.Point (𝟙 (Spec (CommRingCat.of k)))).1
        = (0 : E.Point (D.ideal.subschemeι ≫ E.π)).1
    rw [E.point_zero_val, E.point_zero_val, Category.id_comp]
  calc (((N : ℕ) : ℤ) • E.upt (D := D)).1 = w ≫ D.ideal.subschemeι := hw.symm
    _ = (E.subgroupStructMap D ≫ E.subgroupUnit hD) ≫ D.ideal.subschemeι := by rw [hww]
    _ = (0 : E.Point (D.ideal.subschemeι ≫ E.π)).1 := hz

/-- **KM 1.4.2 over a field (`T`-point form)**: over a field base, a degree-`N` subgroup
divisor kills every point factoring through it — with NO invertibility hypothesis. -/
theorem _root_.ModularCurves.RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors_of_field
    {D : RelEffCartierDiv E.π} (hD : D.IsSubgroup E) {N : ℕ} [NeZero N]
    (hdeg : ∀ s, D.degree s = N) {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of k))
    (Q : E.Point g) (hQ : ∃ h : T ⟶ D.ideal.subscheme, h ≫ D.ideal.subschemeι = Q.1) :
    (N : ℤ) • Q = 0 :=
  RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors_of_upt E
    (RelEffCartierDiv.IsSubgroup.smul_upt_eq_zero_of_field E hD hdeg) g Q hQ

end FieldBox

section InvertibleBox

/-! ### The box at invertible `N` over an arbitrary base

The spreading-out of the field case: the killed fibre-universal points put every fibre of
the divisor scheme inside the finite étale `E[N]`, so the divisor scheme is unramified
over the base; the clopen-equalizer detection engine then globalizes the fibrewise
agreement of the two factorings of `N • upt` and `0`. -/

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- Pulling a point of `E` back along the residue-field point of a `T`-scheme and
base-changing lands it in the field-base situation: a factoring point over a field base
is killed (`smul_eq_zero_of_factors_of_field` after base change). -/
private theorem killed_of_residue_factor {D : RelEffCartierDiv E.π} (hD : D.IsSubgroup E)
    {N : ℕ} [NeZero N] (hdeg : ∀ s : S, D.degree s = N)
    {W : Scheme.{u}} (x : W) (t' : Spec (W.residueField x) ⟶ S) (Q : E.Point t')
    (hQ : ∃ h : Spec (W.residueField x) ⟶ D.ideal.subscheme,
      h ≫ D.ideal.subschemeι = Q.1) :
    (N : ℤ) • Q = 0 := by
  -- base-change the whole situation to the residue field
  have hfac : ∃ h : Spec (W.residueField x) ⟶ (D.baseChange t').ideal.subscheme,
      h ≫ (D.baseChange t').ideal.subschemeι = (Point.asSection E t' Q).1 := by
    rw [RelEffCartierDiv.baseChange_ideal]
    refine (AlgebraicGeometry.Scheme.IdealSheafData.exists_factor_comap_iff D.ideal
      (Limits.pullback.fst E.π t') (Point.asSection E t' Q).1).mpr ?_
    obtain ⟨h, hh⟩ := hQ
    exact ⟨h, hh.trans (Point.asSection_val_fst E t' Q).symm⟩
  have hbc : (N : ℤ) • Point.asSection E t' Q = 0 :=
    RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors_of_field (E.baseChange t')
      (RelEffCartierDiv.IsSubgroup.baseChange E hD t')
      (fun s => degree_baseChange_eq E hdeg t' s) (𝟙 _) (Point.asSection E t' Q) hfac
  have hzero : Point.asSection E t' (0 : E.Point t') = 0 := by
    have h := Point.asSection_zsmul E t' 0 (0 : E.Point t')
    rwa [zero_zsmul, zero_zsmul] at h
  have hinj : Function.Injective (Point.asSection E t') := by
    intro P P' hPP'
    apply Subtype.ext
    have h := congrArg
      (fun s : (E.baseChange t').Point (𝟙 (Spec (W.residueField x))) =>
        s.1 ≫ Limits.pullback.fst E.π t') hPP'
    simpa only [Point.asSection_val_fst] using h
  exact hinj (by rw [Point.asSection_zsmul, hbc, hzero])

/-- **The divisor scheme of a subgroup divisor is unramified at invertible `N`**
(KM 1.4.4(4)-flavoured): each residue fibre is the base-changed divisor scheme over a
field, which the field-level box places as a closed subscheme of the `N`-torsion — finite
étale at invertible `N` (`formallyUnramified_torsionπ`). -/
private theorem formallyUnramified_subgroup_structMap {D : RelEffCartierDiv E.π}
    (hD : D.IsSubgroup E) {N : ℕ} [NeZero N] (hinv : NIsInvertible S N)
    (hdeg : ∀ s : S, D.degree s = N) :
    FormallyUnramified (D.ideal.subschemeι ≫ E.π) := by
  haveI : IsFinite (D.ideal.subschemeι ≫ E.π) := D.finite
  refine FormallyUnramified.of_finite_fiberToSpecResidueField _ (fun y => ?_)
  set t : Spec (S.residueField y) ⟶ S := S.fromSpecResidueField y with ht
  -- the fibre divisor's universal point is killed (field box), so it maps into `E[N]`
  have hupt : (N : ℤ) • (E.baseChange t).upt (D := D.baseChange t) = 0 :=
    RelEffCartierDiv.IsSubgroup.smul_upt_eq_zero_of_field (E.baseChange t)
      (RelEffCartierDiv.IsSubgroup.baseChange E hD t)
      (fun s => degree_baseChange_eq E hdeg t s)
  have hxm : ((E.baseChange t).upt (D := D.baseChange t)).1
        ≫ (E.baseChange t).mulByHom N
      = ((D.baseChange t).ideal.subschemeι ≫ (E.baseChange t).π) ≫ (E.baseChange t).zero := by
    have h1 := congrArg Subtype.val hupt
    rw [(E.baseChange t).point_smul_eq_comp_mulBy _ ((N : ℕ) : ℤ)
      ((E.baseChange t).upt (D := D.baseChange t)), (E.baseChange t).point_zero_val] at h1
    exact h1
  set wtor := (E.baseChange t).pointToTorsion
    ((E.baseChange t).upt (D := D.baseChange t)) hxm with hwtor
  have hwι : wtor ≫ (E.baseChange t).torsionι N
      = (D.baseChange t).ideal.subschemeι :=
    (E.baseChange t).pointToTorsion_torsionι _ hxm
  haveI : IsClosedImmersion (wtor ≫ (E.baseChange t).torsionι N) := by
    rw [hwι]
    exact inferInstanceAs
      (IsClosedImmersion (Scheme.IdealSheafData.subschemeι (D.baseChange t).ideal))
  haveI := (E.baseChange t).torsionι_isClosedImmersion N
  haveI : IsClosedImmersion wtor :=
    IsClosedImmersion.of_comp wtor ((E.baseChange t).torsionι N)
  haveI : IsIso (Limits.pullback.diagonal wtor) := inferInstance
  haveI : FormallyUnramified wtor := inferInstance
  haveI : FormallyUnramified ((E.baseChange t).torsionπ N) :=
    (E.baseChange t).formallyUnramified_torsionπ N (hinv.of_hom t)
  have hqt : wtor ≫ (E.baseChange t).torsionπ N
      = (D.baseChange t).ideal.subschemeι ≫ (E.baseChange t).π :=
    (E.baseChange t).pointToTorsion_torsionπ _ hxm
  haveI hFUqt : FormallyUnramified
      ((D.baseChange t).ideal.subschemeι ≫ (E.baseChange t).π) := by
    rw [← hqt]
    exact MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
  -- transport across the pasted-pullback comparison to the mathlib fibre
  haveI : IsClosedImmersion
      (Limits.pullback.snd D.ideal.subschemeι (Limits.pullback.fst E.π t)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have hι : (Limits.pullback.snd D.ideal.subschemeι
        (Limits.pullback.fst E.π t)).ker.subschemeι
      = inv (Limits.pullback.snd D.ideal.subschemeι
          (Limits.pullback.fst E.π t)).toImage
        ≫ Limits.pullback.snd D.ideal.subschemeι (Limits.pullback.fst E.π t) := by
    rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι]
  have hstruct : (D.baseChange t).ideal.subschemeι ≫ (E.baseChange t).π
      = inv (Limits.pullback.snd D.ideal.subschemeι (Limits.pullback.fst E.π t)).toImage
        ≫ (Limits.pullback.snd D.ideal.subschemeι (Limits.pullback.fst E.π t)
            ≫ Limits.pullback.snd E.π t) := by
    show (Limits.pullback.snd D.ideal.subschemeι (Limits.pullback.fst E.π t)).ker.subschemeι
        ≫ Limits.pullback.snd E.π t = _
    rw [hι, Category.assoc]
  have hsq := (IsPullback.of_hasPullback D.ideal.subschemeι
    (Limits.pullback.fst E.π t)).paste_vert (IsPullback.of_hasPullback E.π t)
  have hfib : Limits.pullback.snd (D.ideal.subschemeι ≫ E.π) t
      = (hsq.isoPullback.inv
          ≫ (Limits.pullback.snd D.ideal.subschemeι
              (Limits.pullback.fst E.π t)).toImage)
        ≫ ((D.baseChange t).ideal.subschemeι ≫ (E.baseChange t).π) := by
    rw [Category.assoc, Iso.eq_inv_comp]
    show hsq.isoPullback.hom ≫ Limits.pullback.snd (D.ideal.subschemeι ≫ E.π) t
        = (Limits.pullback.snd D.ideal.subschemeι (Limits.pullback.fst E.π t)).toImage
          ≫ ((Limits.pullback.snd D.ideal.subschemeι
              (Limits.pullback.fst E.π t)).ker.subschemeι
            ≫ Limits.pullback.snd E.π t)
    rw [hι]
    simp only [Category.assoc]
    rw [IsIso.hom_inv_id_assoc]
    exact hsq.isoPullback_hom_snd
  show FormallyUnramified (Limits.pullback.snd (D.ideal.subschemeι ≫ E.π) t)
  rw [hfib, MorphismProperty.cancel_left_of_respectsIso @FormallyUnramified]
  exact hFUqt

/-- **Register box `smul_eq_zero_of_factors`, invertible-`N` instance (T-E4F1 — KM 1.4.2
at invertible `N`)**: a subgroup divisor of constant degree `N`, with `N` invertible on
the base, is killed by `N` — every point factoring through it is annihilated by `N`.
Proven WITHOUT the Oort–Tate/Deligne over-`ℤ` black box: the field-base case is the
abstract Deligne theorem through the Γ-convolution dictionary, and the invertible-`N`
unramifiedness of the divisor scheme spreads it out via the clopen-equalizer detection
engine. The general-base box (`ExactOrder.lean:113`) remains the statement-protected
over-`ℤ` project. -/
theorem _root_.ModularCurves.RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors_of_invertible
    {D : RelEffCartierDiv E.π} (hD : D.IsSubgroup E) {N : ℕ} [NeZero N]
    (hinv : NIsInvertible S N) (hdeg : ∀ s : S, D.degree s = N)
    {T : Scheme.{u}} (g : T ⟶ S) (Q : E.Point g)
    (hQ : ∃ h : T ⟶ D.ideal.subscheme, h ≫ D.ideal.subschemeι = Q.1) :
    (N : ℤ) • Q = 0 := by
  refine RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors_of_upt E ?_ g Q hQ
  -- the two factorings of `N • upt` and `0`
  obtain ⟨wN, hwN⟩ := RelEffCartierDiv.IsSubgroup.exists_zsmul_upt_factor E hD ((N : ℕ) : ℤ)
  have hwNq : wN ≫ (D.ideal.subschemeι ≫ E.π) = D.ideal.subschemeι ≫ E.π := by
    rw [← Category.assoc, hwN]
    exact (((N : ℕ) : ℤ) • E.upt (D := D)).2
  set w0 : D.ideal.subscheme ⟶ D.ideal.subscheme :=
    (D.ideal.subschemeι ≫ E.π) ≫ E.subgroupUnit hD with hw0
  have hw0ι : w0 ≫ D.ideal.subschemeι = (D.ideal.subschemeι ≫ E.π) ≫ E.zero := by
    rw [hw0, Category.assoc, E.subgroupUnit_subschemeι hD]
    show (D.ideal.subschemeι ≫ E.π) ≫ (0 : E.Point (𝟙 S)).1 = _
    rw [E.point_zero_val, Category.id_comp]
  have hw0q : w0 ≫ (D.ideal.subschemeι ≫ E.π) = D.ideal.subschemeι ≫ E.π := by
    rw [hw0, Category.assoc]
    have h := E.subgroupUnit_over hD
    rw [show E.subgroupUnit hD ≫ D.ideal.subschemeι ≫ E.π = 𝟙 S from h, Category.comp_id]
  -- the unramified detection engine
  haveI : IsFinite (D.ideal.subschemeι ≫ E.π) := D.finite
  haveI : LocallyOfFinitePresentation (D.ideal.subschemeι ≫ E.π) := D.lfp
  haveI : LocallyOfFiniteType (D.ideal.subschemeι ≫ E.π) := inferInstance
  haveI : FormallyUnramified (D.ideal.subschemeι ≫ E.π) :=
    formallyUnramified_subgroup_structMap E hD hinv hdeg
  set XO : Over S := Over.mk (D.ideal.subschemeι ≫ E.π) with hXO
  haveI : FormallyUnramified XO.hom :=
    formallyUnramified_subgroup_structMap E hD hinv hdeg
  haveI : LocallyOfFiniteType XO.hom := inferInstanceAs
    (LocallyOfFiniteType (D.ideal.subschemeι ≫ E.π))
  set fN : XO ⟶ XO := Over.homMk wN hwNq with hfN
  set f0 : XO ⟶ XO := Over.homMk w0 hw0q with hf0
  have heq : fN = f0 := by
    refine Over.hom_ext_of_unramified_of_surjective fN f0 ?_
    -- every point of the divisor scheme lifts to the equalizer: fibrewise agreement
    intro x
    set gx := D.ideal.subscheme.fromSpecResidueField x with hgx
    have hagree : gx ≫ wN = gx ≫ w0 := by
      rw [← cancel_mono D.ideal.subschemeι, Category.assoc, Category.assoc, hwN, hw0ι]
      -- the pulled point is killed by the field-base box
      set t' : Spec (D.ideal.subscheme.residueField x) ⟶ S :=
        gx ≫ D.ideal.subschemeι ≫ E.π with ht'
      set Px : E.Point t' := ⟨gx ≫ D.ideal.subschemeι, rfl⟩ with hPx
      have hkill : (N : ℤ) • Px = 0 :=
        killed_of_residue_factor E hD hdeg x t' Px ⟨gx, rfl⟩
      have hkill1 := congrArg Subtype.val hkill
      rw [E.point_smul_eq_comp_mulBy _ ((N : ℕ) : ℤ) Px, E.point_zero_val] at hkill1
      have hleft : gx ≫ (((N : ℕ) : ℤ) • E.upt (D := D)).1
          = (gx ≫ D.ideal.subschemeι) ≫ E.mulByHom ((N : ℕ) : ℤ) := by
        rw [E.point_smul_eq_comp_mulBy _ ((N : ℕ) : ℤ) (E.upt (D := D))]
        rw [← Category.assoc]
        rfl
      rw [hleft]
      have hPx1 : (Px.1 : Spec (D.ideal.subscheme.residueField x) ⟶ E.E)
          = gx ≫ D.ideal.subschemeι := rfl
      rw [← hPx1, hkill1, ht']
      rw [← Category.assoc]
      rfl
    -- package the agreement as an equalizer point
    set WO : Over S := Over.mk (gx ≫ D.ideal.subschemeι ≫ E.π) with hWO
    set hmap : WO ⟶ XO := Over.homMk gx rfl with hhmap
    have hcomm : hmap ≫ fN = hmap ≫ f0 := by
      apply CategoryTheory.Over.OverMorphism.ext
      rw [CategoryTheory.Over.comp_left, CategoryTheory.Over.comp_left]
      show gx ≫ wN = gx ≫ w0
      exact hagree
    set lft := equalizer.lift hmap hcomm with hlft
    have hfaceq : lft ≫ equalizer.ι fN f0 = hmap := equalizer.lift_ι _ _
    obtain ⟨pt⟩ : Nonempty ↑(Spec (D.ideal.subscheme.residueField x)) := inferInstance
    refine ⟨lft.left.base pt, ?_⟩
    have hcompleft : lft.left ≫ (equalizer.ι fN f0).left = gx := by
      have h := congrArg (fun m : WO ⟶ XO => m.left) hfaceq
      rw [hhmap] at h
      exact h
    have happly : (equalizer.ι fN f0).left.base (lft.left.base pt)
        = (lft.left ≫ (equalizer.ι fN f0).left).base pt := by
      rw [Scheme.Hom.comp_base, TopCat.comp_app]
    rw [happly, hcompleft]
    exact Scheme.fromSpecResidueField_apply x pt
  -- read off the killing of the universal point
  have hww : wN = w0 := by
    have h := congrArg (fun m : XO ⟶ XO => m.left) heq
    rw [hfN, hf0] at h
    exact h
  refine Subtype.ext ?_
  calc (((N : ℕ) : ℤ) • E.upt (D := D)).1 = wN ≫ D.ideal.subschemeι := hwN.symm
    _ = w0 ≫ D.ideal.subschemeι := by rw [hww]
    _ = (D.ideal.subschemeι ≫ E.π) ≫ E.zero := hw0ι
    _ = (0 : E.Point (D.ideal.subschemeι ≫ E.π)).1 := (E.point_zero_val _).symm

end InvertibleBox

section ExactOrderConsumers

/-! ### KM 1.4.2 / 1.4.4(3) for `orderDivisor` at invertible `N` (the T-E4F1/T-E4F2
consumer lemmas) -/

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- **KM 1.4.2 at invertible `N` (T-E4F1)**: a point of Drinfeld exact order `N`, with
`N` invertible on the base, satisfies `N • P = 0`. Invertible-`N` counterpart of
`Section.HasExactOrder.smul_eq_zero` (which rests on the statement-protected over-`ℤ`
box). -/
theorem Section.HasExactOrder.smul_eq_zero_of_invertible {P : E.Section} {N : ℕ}
    [NeZero N] (hinv : NIsInvertible S N) (h : P.HasExactOrder E N) :
    (N : ℤ) • P = 0 := by
  haveI hsep : IsSeparated E.π := inferInstance
  have hpos : IsSeparated E.π ∧ SmoothOfRelativeDimension 1 E.π := ⟨hsep, E.smooth⟩
  have hdeg : ∀ s, (P.orderDivisor E N).degree s = N := fun s =>
    RelEffCartierDiv.sectionsDivisor_degree E.π E.smooth _ s
  refine RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors_of_invertible E h hinv hdeg
    (𝟙 S) P ?_
  have hideal : (P.orderDivisor E N).ideal =
      ∏ a : Fin N, Scheme.Hom.ker (((((a : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S))).1 := by
    rw [Section.orderDivisor, RelEffCartierDiv.sectionsDivisor, dif_pos hpos]
  have h0 : (((((0 : Fin N) : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S)) = P := by
    simp
  have hle : (P.orderDivisor E N).ideal ≤ Scheme.Hom.ker P.1 := by
    rw [hideal]
    have hle0 : (∏ a : Fin N,
        Scheme.Hom.ker (((((a : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S))).1) ≤
        Scheme.Hom.ker (((((0 : Fin N) : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S)).1 := by
      intro U
      have hprod : (∏ a : Fin N,
          Scheme.Hom.ker (((((a : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S))).1).ideal =
          ∏ a : Fin N,
            (Scheme.Hom.ker (((((a : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S))).1).ideal :=
        map_prod (Scheme.IdealSheafData.idealMonoidHom E.E) _ _
      calc (∏ a : Fin N,
          Scheme.Hom.ker (((((a : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S))).1).ideal U
          = ∏ a : Fin N, (Scheme.Hom.ker
              (((((a : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S))).1).ideal U := by
            rw [hprod]
            exact Finset.prod_apply U Finset.univ _
        _ ≤ _ :=
          Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ (0 : Fin N)))
    rw [h0] at hle0
    exact hle0
  haveI hPc : IsClosedImmersion P.1 := by
    have h1 : IsClosedImmersion (P.1 ≫ E.π) := by
      rw [P.2]
      infer_instance
    exact IsClosedImmersion.of_comp P.1 E.π
  refine ⟨P.1.toImage ≫ Scheme.IdealSheafData.inclusion hle, ?_⟩
  rw [Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  exact P.1.toImage_imageι

end ExactOrderConsumers

section FieldDistinct

variable {k : Type u} [Field k] [IsAlgClosed k]
  (E : EllipticCurve (Spec (CommRingCat.of k)))

/-- **KM 1.4.4 (1)⟹(3) over `k̄` (T-E4F2)**: an exact-order-`N` point over an
algebraically closed field with `N` invertible has all proper multiples nonzero. Route:
the order-divisor scheme is finite étale of rank `N` (killed universal point ⟹ closed
subscheme of the étale `E[N]`), so it has exactly `N` sections; the exhaustion engine
pins every section as a multiple of `P`, and a relation `a • P = 0` would leave at most
`a < N` distinct multiples. -/
theorem Section.HasExactOrder.nsmul_ne_zero_of_field {P : E.Section} {N : ℕ} [NeZero N]
    (hinv : NIsInvertible (Spec (CommRingCat.of k)) N) (h : P.HasExactOrder E N)
    {a : ℕ} (ha0 : 0 < a) (haN : a < N) :
    (a : ℤ) • P ≠ 0 := by
  intro hcon
  classical
  haveI : IsSepClosed k := IsSepClosed.of_isAlgClosed k
  have hpos : IsSeparated E.π ∧ SmoothOfRelativeDimension 1 E.π :=
    ⟨inferInstance, E.smooth⟩
  have hdeg : ∀ s, (P.orderDivisor E N).degree s = N := fun s =>
    RelEffCartierDiv.sectionsDivisor_degree E.π E.smooth _ s
  set D := P.orderDivisor E N with hDdef
  set q : D.ideal.subscheme ⟶ Spec (CommRingCat.of k) := D.ideal.subschemeι ≫ E.π with hq
  -- the divisor scheme is finite étale over `k` of rank `N`
  have hupt : (N : ℤ) • E.upt (D := D) = 0 :=
    RelEffCartierDiv.IsSubgroup.smul_upt_eq_zero_of_field E h hdeg
  have hxm : (E.upt (D := D)).1 ≫ E.mulByHom N = q ≫ E.zero := by
    have h1 := congrArg Subtype.val hupt
    rw [E.point_smul_eq_comp_mulBy _ ((N : ℕ) : ℤ) (E.upt (D := D)),
      E.point_zero_val] at h1
    exact h1
  set wtor := E.pointToTorsion (E.upt (D := D)) hxm with hwtor
  have hwι : wtor ≫ E.torsionι N = D.ideal.subschemeι :=
    E.pointToTorsion_torsionι _ hxm
  haveI : IsClosedImmersion (wtor ≫ E.torsionι N) := by
    rw [hwι]
    infer_instance
  haveI := E.torsionι_isClosedImmersion N
  haveI : IsClosedImmersion wtor := IsClosedImmersion.of_comp wtor (E.torsionι N)
  haveI : IsIso (Limits.pullback.diagonal wtor) := inferInstance
  haveI : FormallyUnramified wtor := inferInstance
  haveI : FormallyUnramified (E.torsionπ N) := E.formallyUnramified_torsionπ N hinv
  have hqt : wtor ≫ E.torsionπ N = q := E.pointToTorsion_torsionπ _ hxm
  haveI hFU : FormallyUnramified q := by
    rw [← hqt]
    exact MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
  haveI : IsFinite q := D.finite
  haveI : AlgebraicGeometry.Flat q := D.flat
  haveI : LocallyOfFinitePresentation q := D.lfp
  haveI : Etale q := Etale.of_formallyUnramified_of_flat q
  obtain ⟨x₀⟩ : Nonempty ↑(Spec (CommRingCat.of k)) := inferInstance
  -- exactly `N` sections
  have hcount : Nat.card { s : Spec (CommRingCat.of k) ⟶ D.ideal.subscheme //
      s ≫ q = 𝟙 (Spec (CommRingCat.of k)) } = N := by
    rw [natCard_sections_eq_finrank q x₀]
    exact hdeg x₀
  -- every section is a multiple of `P` (exhaustion), and multiples repeat mod `a`
  have hmod : ∀ b : ℕ, ((b : ℕ) : ℤ) • P = (((b % a : ℕ)) : ℤ) • P := by
    intro b
    conv_lhs => rw [show b = a * (b / a) + b % a from (Nat.div_add_mod b a).symm]
    push_cast
    rw [add_zsmul, mul_comm, mul_zsmul, hcon, smul_zero, zero_add]
  have hexh : ∀ s : { s : Spec (CommRingCat.of k) ⟶ D.ideal.subscheme //
      s ≫ q = 𝟙 (Spec (CommRingCat.of k)) },
      ∃ r : Fin a, s.1 ≫ D.ideal.subschemeι = (((r : ℕ) : ℤ) • P : E.Point (𝟙 _)).1 := by
    rintro ⟨s, hs⟩
    have hover : (s ≫ D.ideal.subschemeι) ≫ E.π = 𝟙 (Spec (CommRingCat.of k)) := by
      rw [Category.assoc]
      exact hs
    obtain ⟨-, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      E.E.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ ((s ≫ D.ideal.subschemeι)
          (default : ↑(Spec (CommRingCat.of k))))) isOpen_univ
    obtain ⟨j, hj⟩ := RelEffCartierDiv.point_eq_section_of_factors (π := E.π)
      (fun b : Fin N => ((((b : ℕ) : ℤ) + 1) • P : E.Point (𝟙 _)))
      hpos (s ≫ D.ideal.subschemeι) hover
      (by
        rw [show (RelEffCartierDiv.sectionsDivisor E.π
            (fun b : Fin N => ((((b : ℕ) : ℤ) + 1) • P : E.Point (𝟙 _))))
          = P.orderDivisor E N from rfl]
        exact ⟨s, rfl⟩)
      ⟨V, hV⟩ hxV
    refine ⟨⟨((j : ℕ) + 1) % a, Nat.mod_lt _ ha0⟩, ?_⟩
    rw [hj]
    have h1 : ((((j : ℕ) : ℤ) + 1) • P : E.Point (𝟙 (Spec (CommRingCat.of k))))
        = ((((j : ℕ) + 1 : ℕ) : ℤ) • P : E.Point (𝟙 _)) := by
      push_cast
      rfl
    rw [h1, hmod ((j : ℕ) + 1)]
  -- the injective map from sections into at most `a` multiples
  haveI hfinsec : Finite { s : Spec (CommRingCat.of k) ⟶ D.ideal.subscheme //
      s ≫ q = 𝟙 (Spec (CommRingCat.of k)) } := finite_sections q
  set F : { s : Spec (CommRingCat.of k) ⟶ D.ideal.subscheme //
      s ≫ q = 𝟙 (Spec (CommRingCat.of k)) } → Set.range (fun r : Fin a =>
        (((r : ℕ) : ℤ) • P : E.Point (𝟙 (Spec (CommRingCat.of k)))).1) :=
    fun s => ⟨s.1 ≫ D.ideal.subschemeι, by
      obtain ⟨r, hr⟩ := hexh s
      exact ⟨r, hr.symm⟩⟩ with hF
  have hFinj : Function.Injective F := by
    intro s s' hss
    have h1 : s.1 ≫ D.ideal.subschemeι = s'.1 ≫ D.ideal.subschemeι :=
      congrArg Subtype.val hss
    exact Subtype.ext ((cancel_mono D.ideal.subschemeι).mp h1)
  haveI hfinR : Finite ↥(Set.range (fun r : Fin a =>
      (((r : ℕ) : ℤ) • P : E.Point (𝟙 (Spec (CommRingCat.of k)))).1)) :=
    (Set.finite_range _).to_subtype
  have hle1 : Nat.card { s : Spec (CommRingCat.of k) ⟶ D.ideal.subscheme //
      s ≫ q = 𝟙 (Spec (CommRingCat.of k)) }
      ≤ Nat.card ↥(Set.range (fun r : Fin a =>
        (((r : ℕ) : ℤ) • P : E.Point (𝟙 (Spec (CommRingCat.of k)))).1)) :=
    Nat.card_le_card_of_injective F hFinj
  have hle2 : Nat.card ↥(Set.range (fun r : Fin a =>
      (((r : ℕ) : ℤ) • P : E.Point (𝟙 (Spec (CommRingCat.of k)))).1)) ≤ a := by
    have hsurj : Function.Surjective (fun r : Fin a =>
        (⟨(((r : ℕ) : ℤ) • P : E.Point (𝟙 (Spec (CommRingCat.of k)))).1, r, rfl⟩ :
          Set.range (fun r : Fin a =>
            (((r : ℕ) : ℤ) • P : E.Point (𝟙 (Spec (CommRingCat.of k)))).1))) := by
      rintro ⟨y, r, hr⟩
      exact ⟨r, Subtype.ext hr⟩
    calc Nat.card ↥(Set.range (fun r : Fin a =>
        (((r : ℕ) : ℤ) • P : E.Point (𝟙 (Spec (CommRingCat.of k)))).1))
        ≤ Nat.card (Fin a) := Nat.card_le_card_of_surjective _ hsurj
      _ = a := by simp
  omega

end FieldDistinct

section GeometricDistinct

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- **KM 1.4.4 (1)⟹(3) at a geometric point (T-E4F2)** — the invertible-`N` bypass of
the char-`p` jet keystone `pull_nsmul_jetData`: an exact-order-`N` point with `N`
invertible has all proper multiples nonzero at every algebraically closed geometric
point. Base-change to the fibre + `nsmul_ne_zero_of_field`, transported through the
base-change point dictionary (the `geometric_input` pattern). -/
theorem Section.HasExactOrder.pull_nsmul_ne_zero_of_invertible {P : E.Section} {N : ℕ}
    [NeZero N] (hinv : NIsInvertible S N) (h : P.HasExactOrder E N)
    (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S)
    {a : ℕ} (ha0 : 0 < a) (haN : a < N) :
    (a : ℤ) • Point.pull E t P ≠ 0 := by
  intro hcon
  have h_t : Section.HasExactOrder (E.baseChange t)
      (Point.asSection E t (Point.pull E t P)) N :=
    Section.HasExactOrder.baseChange E h t
  have hdist := Section.HasExactOrder.nsmul_ne_zero_of_field (E.baseChange t)
    (hinv.of_hom t) h_t ha0 haN
  apply hdist
  set ψ := (Point.baseChangeEquiv E t (𝟙 (Spec (CommRingCat.of k)))).trans
    (Point.castBase E (Category.id_comp t)) with hψ
  have hgen : ψ (Point.asSection E t (Point.pull E t P)) = Point.pull E t P := by
    refine Subtype.ext ?_
    have h1 : (ψ (Point.asSection E t (Point.pull E t P))).1
        = ((Point.baseChangeEquiv E t (𝟙 _)) (Point.asSection E t (Point.pull E t P))).1 :=
      Point.castBase_coe E (Category.id_comp t)
        ((Point.baseChangeEquiv E t (𝟙 _)) (Point.asSection E t (Point.pull E t P)))
    have h2 : ((Point.baseChangeEquiv E t (𝟙 _)) (Point.asSection E t (Point.pull E t P))).1
        = (Point.asSection E t (Point.pull E t P)).1 ≫ pullback.fst E.π t :=
      Point.baseChangeEquiv_apply_coe E t _ _
    have h3 : (Point.asSection E t (Point.pull E t P)).1 ≫ pullback.fst E.π t
        = (Point.pull E t P).1 := Point.asSection_val_fst E t _
    exact (h1.trans h2).trans h3
  have hclaim : ψ ((a : ℤ) • Point.asSection E t (Point.pull E t P))
      = (a : ℤ) • Point.pull E t P := by
    have h1 : ψ ((a : ℤ) • Point.asSection E t (Point.pull E t P))
        = (a : ℤ) • ψ (Point.asSection E t (Point.pull E t P)) :=
      ψ.toAddMonoidHom.map_zsmul _ _
    rw [h1, hgen]
  have h0 : ψ (0 : (E.baseChange t).Point (𝟙 (Spec (CommRingCat.of k)))) = 0 :=
    ψ.toAddMonoidHom.map_zero
  exact ψ.injective (hclaim.trans (hcon.trans h0.symm))

end GeometricDistinct

end EllipticCurve

end ModularCurves
