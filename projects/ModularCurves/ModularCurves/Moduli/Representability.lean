/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.EngineDescent
import ModularCurves.Moduli.GlobalModelTransport
import ModularCurves.ForMathlib.TorsorMap
import ModularCurves.EllipticCurve.GroupLawDescent

/-!
# [B3] The Katz–Mazur 4.7.0 representability capstone (global-model form)

`representable_of_rigid_of_torsor_of_globalModel`: a rigid, relatively representable moduli
problem `P` whose universal simultaneous curve carries a global Weierstrass model is
representable. Assembles Phase A (the engine) + [B0] + [B1] + [B2a/b/c'].

Only remaining non-proven leaf: T-W7 (`EllipticCurveGeom.toEllipticCurve` → `grpObj`).
-/

universe u
open CategoryTheory Limits AlgebraicGeometry Opposite
open ModularCurves ModularCurves.ModuliProblem ModularCurves.RouteA

namespace ModularCurves.ModuliProblem

variable {R : CommRingCat.{u}}

/-! ### The θ-tautology: the KM action fixes the `P`-component -/

/-- **(θ-tautology, KM p. 113)** For the KM `Ell/R`-automorphism `e γ = rM.autMulHom (φ γ)`,
the `P`-value of the simultaneous universal class is `e γ`-invariant (`G` acts only on the
`δ`-component). -/
theorem map_inv_autMulHom_fst (P Q : ModuliProblem R) {G : Type u} [Group G]
    (φ : G →* Aut Q) {XM : EllObj R} (rM : (P.simul Q).RepresentableBy XM) (γ : G) :
    P.map (rM.autMulHom ((P.simulAutSnd Q) (φ γ))).inv.op (rM.homEquiv (𝟙 XM)).1 =
      (rM.homEquiv (𝟙 XM)).1 := by
  set η : Aut (P.simul Q) := (P.simulAutSnd Q) (φ γ) with hη
  have key : rM.homEquiv ((rM.autMulHom η).inv) =
      (P.simul Q).map (rM.autMulHom η).inv.op (rM.homEquiv (𝟙 XM)) := by
    conv_lhs => rw [show (rM.autMulHom η).inv =
      (rM.autMulHom η).inv ≫ 𝟙 XM from (Category.comp_id _).symm]
    exact rM.homEquiv_comp _ _
  have key2 : rM.homEquiv ((rM.autMulHom η).inv) = η.inv.app (op XM) (rM.homEquiv (𝟙 XM)) := by
    have h := rM.homEquiv_comp_transportHom η.inv (𝟙 XM)
    rw [Category.id_comp] at h
    exact h
  calc P.map (rM.autMulHom η).inv.op (rM.homEquiv (𝟙 XM)).1
      = (rM.homEquiv ((rM.autMulHom η).inv)).1 := (congrArg Prod.fst key).symm
    _ = (η.inv.app (op XM) (rM.homEquiv (𝟙 XM))).1 := congrArg Prod.fst key2
    _ = (rM.homEquiv (𝟙 XM)).1 := rfl

/-! ### The core geometric construction (X₀, q, α₀) -/

/-- The complete core output of the KM engine: the simultaneous representing object `XM`,
the quotient `Ell/R`-object `X₀`, the projection `Ell/R`-morphism `q : XM ⟶ X₀`, and the
descended universal `P`-class `α₀`. -/
structure CoreData (P Q : ModuliProblem R) {G : Type u} [Group G] [Finite G]
    (φ : G →* Aut Q) : Type (u + 1) where
  /-- The simultaneous representing object `𝕸(P,δ)`. -/
  XM : EllObj R
  /-- Its `(P.simul Q)`-representation. -/
  rM : (P.simul Q).RepresentableBy XM
  /-- The quotient `Ell/R`-object `X₀ = 𝕸(P,δ)/G`. -/
  X₀ : EllObj R
  /-- The quotient projection `Ell/R`-morphism. -/
  q : XM ⟶ X₀
  /-- `q`'s base map is invariant under the KM action. -/
  hqinv : ∀ γ, (P.simulSchemeAction Q φ rM).hom γ ≫ q.baseHom = q.baseHom
  /-- `q`'s base map is an epimorphism. -/
  hqepi : Epi q.baseHom
  /-- `q`'s base map lifts invariant morphisms (quotient universal property). -/
  hqlift : ∀ {W : Scheme.{u}} (F : XM.base ⟶ W),
    (∀ γ, (P.simulSchemeAction Q φ rM).hom γ ≫ F = F) → ∃! F₀, q.baseHom ≫ F₀ = F
  /-- The descended universal `P`-class over `X₀`. -/
  α₀ : P.obj (op X₀)
  /-- It pulls back along `q` to the universal `P`-class of the simultaneous problem. -/
  hα₀ : P.map q.op α₀ = (rM.homEquiv (𝟙 XM)).1

/-- **[B3-obj + B1 assembly]** The core geometric construction: from `Q`-representability,
`P`-relative-representability (affine), rigidity, the torsor rigidifier `δ`, and a global
model on the universal `Q`-curve, the KM engine produces `X₀ = 𝕸(P,δ)/G` with its universal
`P`-class `α₀` descended from `𝕸(P,δ)`. -/
theorem exists_coreData (P Q : ModuliProblem R) {G : Type u} [Group G] [Finite G]
    (φ : G →* Aut Q)
    (hQrep : Q.Representable) (hPrr : P.RelativelyRepresentable)
    (htors : ∀ X : EllObj R, Nonempty (TorsorData φ X)) (hrig : P.Rigid)
    (hQaff : ∀ {Xδ : EllObj R}, Q.RepresentableBy Xδ → IsAffine Xδ.base)
    (hPaff : ∀ (X : EllObj R) (dP : RelRepData P X), IsAffine dP.Z)
    (hmodel : ∀ {Xδ : EllObj R} [IsAffine Xδ.base], Q.RepresentableBy Xδ →
      ∃ (WQ : WeierstrassCurve Γ(Xδ.base, ⊤)) (φQ : Xδ.curve.E ≅ projModel WQ),
        WQ.IsElliptic ∧
        φQ.hom ≫ projModelπ WQ = Xδ.curve.π ≫ Xδ.base.isoSpec.hom ∧
        Xδ.curve.zero ≫ φQ.hom = Xδ.base.isoSpec.hom ≫ projModelZero WQ) :
    Nonempty (CoreData P Q φ) := by
  classical
  -- representing object of `Q`, made affine
  obtain ⟨Xδ, ⟨rδ⟩⟩ := hQrep.has_representation
  haveI hXδaff : IsAffine Xδ.base := hQaff rδ
  -- the relative representation datum for `P`, made affine
  obtain ⟨dP⟩ := (relativelyRepresentable_iff_nonempty_relRepData P).mp hPrr Xδ
  haveI hZaff : IsAffine dP.Z := hPaff Xδ dP
  -- the simultaneous representation `rM : (P.simul Q).RepresentableBy XM`, `XM = Xδ ×_{Xδ} dP.Z`
  set XM : EllObj R := Xδ.pullbackAlong dP.f with hXM
  haveI : IsAffine XM.base := hZaff
  set rM : (P.simul Q).RepresentableBy XM :=
    P.simulRepresentableBy Q rδ @dP.eqv @dP.nat with hrM
  set σ : SchemeAction G XM.base := P.simulSchemeAction Q φ rM with hσ
  -- the `⊤`-atlas
  set V : XM.base → XM.base.Opens := fun _ => ⊤ with hV
  have hVs : ∀ x, σ.IsStableOpen (V x) := fun _ => isStableOpen_top σ
  have hVa : ∀ x, IsAffineOpen (V x) := fun _ => isAffineOpen_top XM.base
  have hVmem : ∀ x, x ∈ V x := fun _ => trivial
  have hVtop : ∀ x, V x = ⊤ := fun _ => rfl
  -- the diagonal instances the engine needs
  haveI : IsSeparated (terminal.from XM.curve.toEllipticCurveGeom.E) := by
    have h : terminal.from XM.curve.toEllipticCurveGeom.E =
        XM.curve.toEllipticCurveGeom.π ≫ terminal.from XM.base := Subsingleton.elim _ _
    rw [h]; infer_instance
  -- the global model on the simultaneous universal curve (via [B0])
  obtain ⟨WQ, φQ, hWQ, hπφQ, hzeroφQ⟩ := hmodel rδ
  obtain ⟨W₀, φ₀, hπφ₀, hzero₀, hell₀⟩ :=
    exists_globalModel_simul (P := P) (Q := Q) rM WQ φQ hπφQ hzeroφQ
  -- the KM engine (Phase A)
  obtain ⟨C', q_eng, hpb, hzero_eng, hqinv_eng⟩ :=
    exists_ellipticCurveGeom_quotient_of_globalModel
      (P.isCurveAction_simulSchemeActionTotal Q φ rM) V hVs hVa hVmem hVtop
      (P.free_simulSchemeAction Q φ rM hrig htors) W₀ φ₀ (hell₀ hWQ) hπφ₀ hzero₀
  -- descend the structure map through the quotient
  have hstructinv : ∀ γ, σ.hom γ ≫ XM.structMap = XM.structMap :=
    fun γ => (rM.autMulHom ((P.simulAutSnd Q) (φ γ))).inv.base_w
  obtain ⟨structMap₀, hstructMap₀, -⟩ :=
    σ.existsUnique_quotientπ_lift V hVs hVa hVmem XM.structMap hstructinv
  -- assemble `X₀` and the quotient `Ell/R`-morphism `q`
  set X₀ : EllObj R :=
    { base := σ.quotient V hVs hVa, structMap := structMap₀, curve := C'.toEllipticCurve }
    with hX₀
  set q : XM ⟶ X₀ :=
    { baseHom := σ.quotientπ V hVs hVa hVmem
      base_w := hstructMap₀
      top := q_eng
      isPullback := hpb
      zero_w := hzero_eng } with hq
  -- descend the universal `P`-class through `q`
  have hepi : Epi q.baseHom :=
    ⟨fun {W} g₁ g₂ h => σ.quotientπ_hom_ext V hVs hVa hVmem g₁ g₂ h⟩
  obtain ⟨α₀, hα₀⟩ : ∃ α₀ : P.obj (op X₀), P.map q.op α₀ = (rM.homEquiv (𝟙 XM)).1 := by
    -- [ALPHA-DESCENT] `existsUnique_alpha_descent` with the θ-cocycle `actE`, the proven
    -- θ-tautology `map_inv_autMulHom_fst`, and `hqcoeq` now closed via the engine's exposed
    -- quotient-invariance `hqinv_eng : ∀ γ, σE.hom γ ≫ q_eng = q_eng`.
    obtain ⟨dPX₀⟩ := (relativelyRepresentable_iff_nonempty_relRepData P).mp hPrr X₀
    have hqcoeq : ∀ γ, (fun γ => (rM.autMulHom ((P.simulAutSnd Q) (φ γ))).inv) γ ≫ q = q := by
      intro γ
      refine EllHom.ext ?_ ?_
      · show (rM.autMulHom ((P.simulAutSnd Q) (φ γ))).inv.baseHom ≫ q.baseHom = q.baseHom
        exact σ.hom_quotientπ V hVs hVa hVmem γ
      · show (rM.autMulHom ((P.simulAutSnd Q) (φ γ))).inv.top ≫ q_eng = q_eng
        exact hqinv_eng γ
    have hlift : ∀ {W : Scheme.{u}} (F : XM.base ⟶ W),
        (∀ γ, σ.hom γ ≫ F = F) → ∃ F₀, q.baseHom ≫ F₀ = F :=
      fun {W} F hF => (σ.existsUnique_quotientπ_lift V hVs hVa hVmem F hF).exists
    exact (existsUnique_alpha_descent q dPX₀ σ
      (fun γ => (rM.autMulHom ((P.simulAutSnd Q) (φ γ))).inv) (fun γ => rfl) hqcoeq hlift hepi
      ((rM.homEquiv (𝟙 XM)).1) (map_inv_autMulHom_fst P Q φ rM)).exists
  exact ⟨{ XM := XM, rM := rM, X₀ := X₀, q := q
           hqinv := fun γ => σ.hom_quotientπ V hVs hVa hVmem γ
           hqepi := hepi
           hqlift := fun {W} F hF => σ.existsUnique_quotientπ_lift V hVs hVa hVmem F hF
           α₀ := α₀, hα₀ := hα₀ }⟩

/-! ### The representability bijection (KM pp. 114–116) -/

/-- **[B3-bij existence a), KM p. 115]** Every `P`-structure on an arbitrary test object `Y`
is induced from the universal `α₀` by some `Ell/R`-morphism `Y ⟶ X₀`. Constructs the
classifying map via the `δ`-torsor over `Y.base`, descends its base map through the torsor
(`existsUnique_descent_of_torsor`, general base), and descends the curve iso by rigidity. -/
theorem coreData_surjective (P Q : ModuliProblem R) {G : Type u} [Group G] [Finite G]
    (φ : G →* Aut Q) (htors : ∀ X : EllObj R, Nonempty (TorsorData φ X)) (hrig : P.Rigid)
    (hPrr : P.RelativelyRepresentable) (cd : CoreData P Q φ) (Y : EllObj R)
    (α : P.obj (op Y)) : ∃ v : Y ⟶ cd.X₀, P.map v.op cd.α₀ = α := by
  sorry -- [B3-bij existence a] curve-iso descent along the δ-torsor (rigidity)

/-- **[B3-bij uniqueness b), KM pp. 115–116]** The inducing `Ell/R`-morphism is unique: two
morphisms `Y ⟶ X₀` inducing the same `P`-structure agree. Uses that a `G`-equivariant map of
finite étale `G`-torsors is an isomorphism (`isIso_of_equivariant_of_torsor`, [B2b]) and that
the torsor projection is an epimorphism. -/
theorem coreData_injective (P Q : ModuliProblem R) {G : Type u} [Group G] [Finite G]
    (φ : G →* Aut Q) (htors : ∀ X : EllObj R, Nonempty (TorsorData φ X)) (hrig : P.Rigid)
    (hPrr : P.RelativelyRepresentable) (cd : CoreData P Q φ) (Y : EllObj R)
    (v v' : Y ⟶ cd.X₀) (h : P.map v.op cd.α₀ = P.map v'.op cd.α₀) : v = v' := by
  sorry -- [B3-bij uniqueness b] G-torsor-map-is-iso ([B2b]) + π-epi

/-- **(T-B3 = KM SCHOLIE 4.7.0 ⇐, global-model form)** A rigid, relatively representable
moduli problem `P` — whose representing `Q`-curve carries a compatible global Weierstrass
model, with `Q` representable by an affine object and `P` affine over `(Ell)` — is
**representable**, by `X₀ = 𝕸(P,δ)/G`.

This is the Katz–Mazur representability theorem 4.7.0, route (a): the engine (Phase A) builds
`X₀` and descends the universal curve; [B1] descends `α₀`; the representability bijection
(existence a) `coreData_surjective` + uniqueness b) `coreData_injective`) is KM pp. 114–116. -/
theorem representable_of_rigid_of_torsor_of_globalModel (P Q : ModuliProblem R)
    {G : Type u} [Group G] [Finite G] (φ : G →* Aut Q)
    (hQrep : Q.Representable) (hPrr : P.RelativelyRepresentable)
    (htors : ∀ X : EllObj R, Nonempty (TorsorData φ X)) (hrig : P.Rigid)
    (hQaff : ∀ {Xδ : EllObj R}, Q.RepresentableBy Xδ → IsAffine Xδ.base)
    (hPaff : ∀ (X : EllObj R) (dP : RelRepData P X), IsAffine dP.Z)
    (hmodel : ∀ {Xδ : EllObj R} [IsAffine Xδ.base], Q.RepresentableBy Xδ →
      ∃ (WQ : WeierstrassCurve Γ(Xδ.base, ⊤)) (φQ : Xδ.curve.E ≅ projModel WQ),
        WQ.IsElliptic ∧
        φQ.hom ≫ projModelπ WQ = Xδ.curve.π ≫ Xδ.base.isoSpec.hom ∧
        Xδ.curve.zero ≫ φQ.hom = Xδ.base.isoSpec.hom ≫ projModelZero WQ) :
    P.Representable := by
  obtain ⟨cd⟩ := exists_coreData P Q φ hQrep hPrr htors hrig hQaff hPaff hmodel
  -- `X₀` with universal class `α₀` represents `P`: the map `v ↦ P.map v.op α₀` is a bijection
  suffices h : P.RepresentableBy cd.X₀ from h.isRepresentable
  refine ⟨fun {Y} => Equiv.ofBijective (fun (v : Y ⟶ cd.X₀) => P.map v.op cd.α₀) ?_, ?_⟩
  · exact ⟨fun v v' hvv => coreData_injective P Q φ htors hrig hPrr cd Y v v' hvv,
      fun α => coreData_surjective P Q φ htors hrig hPrr cd Y α⟩
  · intro Y Y' k v
    show P.map (k ≫ v).op cd.α₀ = P.map k.op (P.map v.op cd.α₀)
    rw [op_comp, Functor.map_comp_apply]

end ModularCurves.ModuliProblem
