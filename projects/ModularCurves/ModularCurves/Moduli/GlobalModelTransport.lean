/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.AdditionBaseChange
import ModularCurves.EllipticCurve.GroupLawAxioms
import ModularCurves.Moduli.EngineDescent

/-!
# [B0] T-B0-GLOBALMODEL — the global Weierstrass model transports to `𝕸(𝒫,δ)`

The Katz–Mazur 4.7 engine (`RouteA.exists_ellipticCurveGeom_quotient_of_globalModel`)
consumes a **global** projective Weierstrass model of the universal curve over `𝕸(𝒫,δ)`,
compatible with the structure morphism and the zero section. This file supplies it: the
simul-representing object of `simulRepresentableBy` is `Xδ.pullbackAlong f`, whose curve is
the **chosen pullback** of `Xδ`'s curve along the classifying map `f`, and a compatible
global model is stable under pullback along *any* morphism of affine bases.

* `exists_globalModel_pullback_ringHom` — the abstract core, over a ring hom `ρ : A →+* B`
  with the geometry threaded as hypotheses (Phase A's `lw_chart_at` pattern): the total
  space `pullback p t` of the base-changed curve is isomorphic to `projModel (WQ.map ρ)`,
  compatibly with the projections and the zero sections.
* `exists_globalModel_pullback` — the `Γ(⊤)`-instantiation: `W₀ := WQ.map t.appTop.hom`,
  the corner isos are `isoSpec`, naturality is `Scheme.isoSpec_hom_naturality`. Ellipticity
  is threaded (`WQ.IsElliptic → W₀.IsElliptic`).
* `exists_globalModel_baseChange` — the `EllipticCurve`-record form, for `C.baseChange t`.
* `exists_globalModel_pullbackAlong` — the `Ell/R` form, for `(XQ.pullbackAlong t).curve`.
* `exists_globalModel_simul` — the [B0] statement: the universal curve of the
  simul-representation (`simulRepresentableBy`'s representing object) carries a compatible
  global model. Source: KM 4.7.0 setup (p. 113); the applications (Legendre, Hesse) supply
  the model on `Xδ`.
-/

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve

open scoped Pointwise

universe u

namespace ModularCurves

section TwoRing

variable {A B : Type u} [CommRing A] [CommRing B]

/-- Two-ring form of `isPullback_projModelBaseChange`: the eqToHom-free base-change square
`isPullback_projModelBaseChangeOf` at the definitional target `V.map ρ`. -/
private theorem isPullback_projModelBaseChange_ringHom (ρ : A →+* B) (V : WeierstrassCurve A) :
    IsPullback (projModelBaseChange ρ V) (projModelπ (V.map ρ)) (projModelπ V)
      (Spec.map (CommRingCat.ofHom ρ)) := by
  rw [← projModelBaseChangeOf_rfl ρ V]
  exact isPullback_projModelBaseChangeOf ρ V (V.map ρ) rfl

/-- Two-ring form of `projModelZero_baseChange`: `projModelZero_baseChangeOf` at the
definitional target `V.map ρ`. -/
private theorem projModelZero_baseChange_ringHom (ρ : A →+* B) (V : WeierstrassCurve A) :
    projModelZero (V.map ρ) ≫ projModelBaseChange ρ V
      = Spec.map (CommRingCat.ofHom ρ) ≫ projModelZero V := by
  rw [← projModelBaseChangeOf_rfl ρ V]
  exact projModelZero_baseChangeOf ρ V (V.map ρ) rfl

/-- The base-change square `isPullback_projModelBaseChange_ringHom` with its `Spec B`-corner
transported to `T` along an iso `eT : T ≅ Spec B` intertwining `t` with `Spec ρ` (`hnat`): the
model of `V.map ρ` is a pullback of `projModelπ V` along `t ≫ eS.hom`, with its `T`-leg
`projModelπ (V.map ρ) ≫ eT.inv`. -/
private theorem isPullback_projModelBaseChange_transport (ρ : A →+* B) (V : WeierstrassCurve A)
    {S T : Scheme.{u}} (t : T ⟶ S) (eS : S ≅ Spec (CommRingCat.of A))
    (eT : T ≅ Spec (CommRingCat.of B))
    (hnat : t ≫ eS.hom = eT.hom ≫ Spec.map (CommRingCat.ofHom ρ)) :
    IsPullback (projModelBaseChange ρ V) (projModelπ (V.map ρ) ≫ eT.inv) (projModelπ V)
      (t ≫ eS.hom) := by
  refine (isPullback_projModelBaseChange_ringHom ρ V).of_iso
    (Iso.refl _) (Iso.refl _) eT.symm (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
  · rw [Iso.refl_hom, Iso.symm_hom, Category.id_comp]
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, hnat, Iso.inv_hom_id_assoc]

/-- π-compatibility of the comparison iso `hcurve.isoIsPullback _ _ hmodel` of
`exists_globalModel_pullback_ringHom`, between the curve square `hcurve` and the transported model
square `hmodel`: it carries `projModelπ (WQ.map ρ)` to `pullback.snd p t ≫ eT.hom`. Proved from the
`snd`-leg of the comparison iso (a `calc`, since `pullback.snd p t` occurs in `hcurve`'s own type so
`rw [← isoIsPullback_hom_snd]` would build an ill-typed motive). -/
private theorem globalModel_pullback_isoIsPullback_hom_π (ρ : A →+* B) (WQ : WeierstrassCurve A)
    {E S T : Scheme.{u}} (p : E ⟶ S) (t : T ⟶ S) (φQ : E ≅ projModel WQ)
    (eS : S ≅ Spec (CommRingCat.of A)) (eT : T ≅ Spec (CommRingCat.of B))
    (hcurve : IsPullback (pullback.fst p t ≫ φQ.hom) (pullback.snd p t)
      (projModelπ WQ) (t ≫ eS.hom))
    (hmodel : IsPullback (projModelBaseChange ρ WQ) (projModelπ (WQ.map ρ) ≫ eT.inv)
      (projModelπ WQ) (t ≫ eS.hom)) :
    (hcurve.isoIsPullback _ _ hmodel).hom ≫ projModelπ (WQ.map ρ)
      = pullback.snd p t ≫ eT.hom :=
  calc (hcurve.isoIsPullback _ _ hmodel).hom ≫ projModelπ (WQ.map ρ)
      = ((hcurve.isoIsPullback _ _ hmodel).hom
          ≫ (projModelπ (WQ.map ρ) ≫ eT.inv)) ≫ eT.hom := by
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = pullback.snd p t ≫ eT.hom := by
        rw [hcurve.isoIsPullback_hom_snd _ _ hmodel]

/-- Zero-compatibility of the comparison iso `hcurve.isoIsPullback _ _ hmodel` of
`exists_globalModel_pullback_ringHom`, between the curve square `hcurve` and the transported model
square `hmodel`: it carries the pulled-back zero section `z0` to `eT.hom ≫ projModelZero (WQ.map ρ)`.
Proved by the universal property of the model square `hmodel`, checking both legs — the
`projModelBaseChange ρ WQ` leg via `hz0fst`/`hzeroφQ`/`hnat`/`projModelZero_baseChange_ringHom`, the
`projModelπ (WQ.map ρ) ≫ eT.inv` leg via `hz0snd`/`projModelZero_projModelπ`. -/
private theorem globalModel_pullback_isoIsPullback_hom_zero (ρ : A →+* B) (WQ : WeierstrassCurve A)
    {E S T : Scheme.{u}} (p : E ⟶ S) (t : T ⟶ S) (z : S ⟶ E) (z0 : T ⟶ pullback p t)
    (φQ : E ≅ projModel WQ) (eS : S ≅ Spec (CommRingCat.of A))
    (eT : T ≅ Spec (CommRingCat.of B))
    (hz0fst : z0 ≫ pullback.fst p t = t ≫ z) (hz0snd : z0 ≫ pullback.snd p t = 𝟙 T)
    (hnat : t ≫ eS.hom = eT.hom ≫ Spec.map (CommRingCat.ofHom ρ))
    (hzeroφQ : z ≫ φQ.hom = eS.hom ≫ projModelZero WQ)
    (hcurve : IsPullback (pullback.fst p t ≫ φQ.hom) (pullback.snd p t)
      (projModelπ WQ) (t ≫ eS.hom))
    (hmodel : IsPullback (projModelBaseChange ρ WQ) (projModelπ (WQ.map ρ) ≫ eT.inv)
      (projModelπ WQ) (t ≫ eS.hom)) :
    z0 ≫ (hcurve.isoIsPullback _ _ hmodel).hom = eT.hom ≫ projModelZero (WQ.map ρ) := by
  have hzbc := projModelZero_baseChange_ringHom ρ WQ
  refine hmodel.hom_ext ?_ ?_
  · -- against `projModelBaseChange ρ WQ`
    calc (z0 ≫ (hcurve.isoIsPullback _ _ hmodel).hom) ≫ projModelBaseChange ρ WQ
        = z0 ≫ ((hcurve.isoIsPullback _ _ hmodel).hom ≫ projModelBaseChange ρ WQ) :=
          Category.assoc _ _ _
      _ = z0 ≫ (pullback.fst p t ≫ φQ.hom) := by
          rw [hcurve.isoIsPullback_hom_fst _ _ hmodel]
      _ = (z0 ≫ pullback.fst p t) ≫ φQ.hom := (Category.assoc _ _ _).symm
      _ = (t ≫ z) ≫ φQ.hom := by rw [hz0fst]
      _ = t ≫ (z ≫ φQ.hom) := Category.assoc _ _ _
      _ = t ≫ (eS.hom ≫ projModelZero WQ) := by rw [hzeroφQ]
      _ = (t ≫ eS.hom) ≫ projModelZero WQ := (Category.assoc _ _ _).symm
      _ = (eT.hom ≫ Spec.map (CommRingCat.ofHom ρ)) ≫ projModelZero WQ := by rw [hnat]
      _ = eT.hom ≫ (Spec.map (CommRingCat.ofHom ρ) ≫ projModelZero WQ) :=
          Category.assoc _ _ _
      _ = eT.hom ≫ (projModelZero (WQ.map ρ) ≫ projModelBaseChange ρ WQ) := by rw [hzbc]
      _ = (eT.hom ≫ projModelZero (WQ.map ρ)) ≫ projModelBaseChange ρ WQ :=
          (Category.assoc _ _ _).symm
  · -- against `projModelπ (WQ.map ρ) ≫ eT.inv`
    calc (z0 ≫ (hcurve.isoIsPullback _ _ hmodel).hom)
          ≫ (projModelπ (WQ.map ρ) ≫ eT.inv)
        = z0 ≫ ((hcurve.isoIsPullback _ _ hmodel).hom
            ≫ (projModelπ (WQ.map ρ) ≫ eT.inv)) := Category.assoc _ _ _
      _ = z0 ≫ pullback.snd p t := by rw [hcurve.isoIsPullback_hom_snd _ _ hmodel]
      _ = 𝟙 T := hz0snd
      _ = (eT.hom ≫ projModelZero (WQ.map ρ)) ≫ (projModelπ (WQ.map ρ) ≫ eT.inv) := by
          simp only [Category.assoc, projModelZero_projModelπ_assoc, Iso.hom_inv_id]

/-- **([B0], abstract core)** A compatible global Weierstrass model is stable under base
change of the curve, over an abstract ring hom `ρ : A →+* B` with the geometry threaded as
hypotheses: given corner isos `eS : S ≅ Spec A`, `eT : T ≅ Spec B` intertwining `t` with
`Spec ρ`, a model `φQ : E ≅ projModel WQ` of the total space compatible with `p` and the
zero section transports to a model of the chosen pullback `pullback p t` at `WQ.map ρ`,
again compatible with the projection `pullback.snd p t` and the pulled-back zero section.

The model iso is the comparison of two pullbacks of the cospan
`(projModelπ WQ, t ≫ eS.hom)`: the curve square `pullback p t` (the chosen square pasted
with the iso square of `φQ`) and the model square `projModel (WQ.map ρ)`
(`isPullback_projModelBaseChange` with its `Spec B`-corner transported to `T` along `eT`). -/
theorem exists_globalModel_pullback_ringHom (ρ : A →+* B) {E S T : Scheme.{u}}
    (p : E ⟶ S) (t : T ⟶ S) (z : S ⟶ E) (z0 : T ⟶ pullback p t)
    (hz0fst : z0 ≫ pullback.fst p t = t ≫ z)
    (hz0snd : z0 ≫ pullback.snd p t = 𝟙 T)
    (eS : S ≅ Spec (CommRingCat.of A)) (eT : T ≅ Spec (CommRingCat.of B))
    (hnat : t ≫ eS.hom = eT.hom ≫ Spec.map (CommRingCat.ofHom ρ))
    (WQ : WeierstrassCurve A) (φQ : E ≅ projModel WQ)
    (hπφQ : φQ.hom ≫ projModelπ WQ = p ≫ eS.hom)
    (hzeroφQ : z ≫ φQ.hom = eS.hom ≫ projModelZero WQ) :
    ∃ φ : pullback p t ≅ projModel (WQ.map ρ),
      φ.hom ≫ projModelπ (WQ.map ρ) = pullback.snd p t ≫ eT.hom ∧
      z0 ≫ φ.hom = eT.hom ≫ projModelZero (WQ.map ρ) := by
  -- the curve square: `pullback p t` is a pullback of `projModelπ WQ` along `t ≫ eS.hom`
  have hcurve : IsPullback (pullback.fst p t ≫ φQ.hom) (pullback.snd p t)
      (projModelπ WQ) (t ≫ eS.hom) :=
    (IsPullback.of_hasPullback p t).paste_horiz (IsPullback.of_horiz_isIso ⟨hπφQ⟩)
  -- the model square, with its `Spec B`-corner transported to `T` along `eT`
  have hmodel : IsPullback (projModelBaseChange ρ WQ)
      (projModelπ (WQ.map ρ) ≫ eT.inv) (projModelπ WQ) (t ≫ eS.hom) :=
    isPullback_projModelBaseChange_transport ρ WQ t eS eT hnat
  -- the comparison iso of the two squares, with π- and zero-compatibility
  exact ⟨hcurve.isoIsPullback _ _ hmodel,
    globalModel_pullback_isoIsPullback_hom_π ρ WQ p t φQ eS eT hcurve hmodel,
    globalModel_pullback_isoIsPullback_hom_zero ρ WQ p t z z0 φQ eS eT
      hz0fst hz0snd hnat hzeroφQ hcurve hmodel⟩

end TwoRing

/-- **([B0], the `Γ(⊤)`-form — the CORE deliverable)** The pullback of a globally-modelled
curve along **any** morphism `t : T ⟶ S` of affine bases carries a compatible global model:
if `φQ : E ≅ projModel WQ` is compatible with `p : E ⟶ S` and the section `z` over
`S.isoSpec`, then `pullback p t` is isomorphic to `projModel W₀` for
`W₀ := WQ.map t.appTop.hom`, compatibly with `pullback.snd p t` and the pulled-back section
over `T.isoSpec`. Ellipticity is threaded: `WQ.IsElliptic → W₀.IsElliptic`. -/
theorem exists_globalModel_pullback {E S T : Scheme.{u}} [IsAffine S] [IsAffine T]
    (p : E ⟶ S) (t : T ⟶ S) (z : S ⟶ E) (hzp : z ≫ p = 𝟙 S)
    (WQ : WeierstrassCurve Γ(S, ⊤)) (φQ : E ≅ projModel WQ)
    (hπφQ : φQ.hom ≫ projModelπ WQ = p ≫ S.isoSpec.hom)
    (hzeroφQ : z ≫ φQ.hom = S.isoSpec.hom ≫ projModelZero WQ) :
    ∃ (W₀ : WeierstrassCurve Γ(T, ⊤)) (φ : pullback p t ≅ projModel W₀),
      φ.hom ≫ projModelπ W₀ = pullback.snd p t ≫ T.isoSpec.hom ∧
      pullback.lift (t ≫ z) (𝟙 T)
          (by rw [Category.assoc, hzp, Category.comp_id, Category.id_comp]) ≫ φ.hom
        = T.isoSpec.hom ≫ projModelZero W₀ ∧
      (WQ.IsElliptic → W₀.IsElliptic) := by
  have hnat : t ≫ S.isoSpec.hom
      = T.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom t.appTop.hom) := by
    rw [CommRingCat.ofHom_hom]
    exact (Scheme.isoSpec_hom_naturality t).symm
  obtain ⟨φ, hπ, hzero⟩ := exists_globalModel_pullback_ringHom t.appTop.hom p t z
    (pullback.lift (t ≫ z) (𝟙 T)
      (by rw [Category.assoc, hzp, Category.comp_id, Category.id_comp]))
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    S.isoSpec T.isoSpec hnat WQ φQ hπφQ hzeroφQ
  exact ⟨WQ.map t.appTop.hom, φ, hπ, hzero, fun h => by haveI := h; exact inferInstance⟩

/-- **([B0], `EllipticCurve`-record form)** The base change `C.baseChange t` of a
globally-modelled elliptic curve along any morphism `t : T ⟶ S` of affine bases carries a
compatible global model, elliptic if the given one is. -/
theorem exists_globalModel_baseChange {S : Scheme.{u}} [IsAffine S] (C : EllipticCurve S)
    {T : Scheme.{u}} [IsAffine T] (t : T ⟶ S)
    (WQ : WeierstrassCurve Γ(S, ⊤)) (φQ : C.E ≅ projModel WQ)
    (hπφQ : φQ.hom ≫ projModelπ WQ = C.π ≫ S.isoSpec.hom)
    (hzeroφQ : C.zero ≫ φQ.hom = S.isoSpec.hom ≫ projModelZero WQ) :
    ∃ (W₀ : WeierstrassCurve Γ(T, ⊤)) (φ : (C.baseChange t).E ≅ projModel W₀),
      φ.hom ≫ projModelπ W₀ = (C.baseChange t).π ≫ T.isoSpec.hom ∧
      (C.baseChange t).zero ≫ φ.hom = T.isoSpec.hom ≫ projModelZero W₀ ∧
      (WQ.IsElliptic → W₀.IsElliptic) :=
  exists_globalModel_pullback C.π t C.zero C.zero_π WQ φQ hπφQ hzeroφQ

/-- **([B0], `Ell/R`-form)** The pullback `XQ.pullbackAlong t` of a globally-modelled
`Ell/R`-object along any morphism `t : T ⟶ XQ.base` of affine bases carries a compatible
global model on its curve, elliptic if the given one is. -/
theorem exists_globalModel_pullbackAlong {R : CommRingCat.{u}} (XQ : EllObj R)
    [IsAffine XQ.base] {T : Scheme.{u}} [IsAffine T] (t : T ⟶ XQ.base)
    (WQ : WeierstrassCurve Γ(XQ.base, ⊤)) (φQ : XQ.curve.E ≅ projModel WQ)
    (hπφQ : φQ.hom ≫ projModelπ WQ = XQ.curve.π ≫ XQ.base.isoSpec.hom)
    (hzeroφQ : XQ.curve.zero ≫ φQ.hom = XQ.base.isoSpec.hom ≫ projModelZero WQ) :
    ∃ (W₀ : WeierstrassCurve Γ(T, ⊤)) (φ : (XQ.pullbackAlong t).curve.E ≅ projModel W₀),
      φ.hom ≫ projModelπ W₀ = (XQ.pullbackAlong t).curve.π ≫ T.isoSpec.hom ∧
      (XQ.pullbackAlong t).curve.zero ≫ φ.hom = T.isoSpec.hom ≫ projModelZero W₀ ∧
      (WQ.IsElliptic → W₀.IsElliptic) :=
  exists_globalModel_baseChange XQ.curve t WQ φQ hπφQ hzeroφQ

/-- **([B0] T-B0-GLOBALMODEL — the global model transports to `𝕸(𝒫,δ)`.)** If the
auxiliary problem is representable by an `Ell/R`-object `Xδ` whose curve carries a
compatible global Weierstrass model, then the universal curve of the **simultaneous
problem** — the curve of `simulRepresentableBy`'s representing object `Xδ.pullbackAlong f`,
for `f : Z ⟶ Xδ.base` the relative representing morphism — carries one too, with
`W₀ = WQ.map f.appTop.hom` and ellipticity threaded.

Stated with the simul-representation as a (definitionally inert) hypothesis, pinning the
[B3] interface; the mathematical content is `exists_globalModel_pullbackAlong` at `t := f`,
because the simul-representing object of `simulRepresentableBy` **is** `Xδ.pullbackAlong f`.
Source: KM 4.7.0 setup (p. 113: `𝕸(𝒫,δ) = 𝒫_{E/𝕸(δ)}` and its universal curve is the
pullback of the universal curve over `𝕸(δ)`); the applications (Legendre, Hesse) supply
the model on `Xδ`. -/
theorem exists_globalModel_simul {R : CommRingCat.{u}} {P Q : ModuliProblem R}
    {Xδ : EllObj R} {Z : Scheme.{u}} {f : Z ⟶ Xδ.base}
    [IsAffine Xδ.base] [IsAffine Z]
    (_rM : (P.simul Q).RepresentableBy (Xδ.pullbackAlong f))
    (WQ : WeierstrassCurve Γ(Xδ.base, ⊤)) (φQ : Xδ.curve.E ≅ projModel WQ)
    (hπφQ : φQ.hom ≫ projModelπ WQ = Xδ.curve.π ≫ Xδ.base.isoSpec.hom)
    (hzeroφQ : Xδ.curve.zero ≫ φQ.hom = Xδ.base.isoSpec.hom ≫ projModelZero WQ) :
    ∃ (W₀ : WeierstrassCurve Γ(Z, ⊤)) (φ : (Xδ.pullbackAlong f).curve.E ≅ projModel W₀),
      φ.hom ≫ projModelπ W₀ = (Xδ.pullbackAlong f).curve.π ≫ Z.isoSpec.hom ∧
      (Xδ.pullbackAlong f).curve.zero ≫ φ.hom = Z.isoSpec.hom ≫ projModelZero W₀ ∧
      (WQ.IsElliptic → W₀.IsElliptic) :=
  exists_globalModel_pullbackAlong Xδ f WQ φQ hπφQ hzeroφQ

end ModularCurves
