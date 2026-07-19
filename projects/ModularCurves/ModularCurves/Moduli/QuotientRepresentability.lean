/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.EngineDescent
import ModularCurves.ForMathlib.QuotientTorsor
import ModularCurves.Moduli.GlobalModelTransport
import ModularCurves.ForMathlib.TorsorMap
import ModularCurves.EllipticCurve.GroupLawDescent

/-!
# [B3] The Katz–Mazur 4.7.0 representability capstone (global-model form)

`representable_of_rigid_of_torsor_of_globalModel`: a rigid, relatively representable moduli
problem `P` whose universal simultaneous curve carries a global Weierstrass model is
representable. Assembles Phase A (the engine) + [B0] + [B1] + [B2a/b/c'].

The T-W7 leaf (`EllipticCurveGeom.toEllipticCurve` → `grpObj`) is PROVEN — verified
axiom-clean {propext, Classical.choice, Quot.sound} (v10.330; the group-law enrichment
chain is complete, and no sorryAx reaches this file from the group-law side).
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
  /-- `q`'s base map is a geometric `G`-torsor (`∐_G XM.base ≅ XM.base ×_{X₀.base} XM.base`). -/
  hqtors : IsIso (ModularCurves.torsorCompare q.baseHom (P.simulSchemeAction Q φ rM) hqinv)
  /-- `q`'s base map is surjective (the quotient projection covers `X₀.base`). -/
  hqsurj : Surjective q.baseHom
  /-- `q`'s base map is étale (finite étale `G`-torsor; KM/De-Ga III.2.6.1). -/
  hqetale : Etale q.baseHom
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
           hqtors := σ.isIso_torsorCompare_quotientπ V hVs hVa hVmem
             (P.free_simulSchemeAction Q φ rM hrig htors)
           hqsurj := ⟨σ.quotientπ_surjective V hVs hVa hVmem⟩
           hqetale := σ.etale_quotientπ V hVs hVa hVmem
             (P.free_simulSchemeAction Q φ rM hrig htors)
           α₀ := α₀, hα₀ := hα₀ }⟩

/-! ### The representability bijection (KM pp. 114–116) -/

/-- Local copy of the private `pullbackAlongMap_pullbackAlongπ` from QuotientProblem. -/
private theorem pullbackAlongMap_pullbackAlongπ' (X : EllObj R)
    {T T' : Scheme.{u}} (g : T ⟶ X.base) (k : T' ⟶ T) :
    X.pullbackAlongMap g k ≫ X.pullbackAlongπ g = X.pullbackAlongπ (k ≫ g) := by
  refine EllHom.ext rfl ?_
  show Limits.pullback.map X.curve.π (k ≫ g) X.curve.π g (𝟙 _) k (𝟙 _)
      (by simp) (by simp) ≫ Limits.pullback.fst X.curve.π g =
    Limits.pullback.fst X.curve.π (k ≫ g)
  rw [Limits.pullback.lift_fst, Category.comp_id]

/-- Local copy of the private `map_eqv` from QuotientProblem: presentation-independent
naturality of a relative representation datum. -/
private theorem map_eqv' {P : ModuliProblem R} {X₀ : EllObj R}
    (d₀ : RelRepData P X₀) {T T' : Scheme.{u}}
    {g : T ⟶ X₀.base} {g' : T' ⟶ X₀.base}
    (w : X₀.pullbackAlong g' ⟶ X₀.pullbackAlong g) (k : T' ⟶ T)
    (hbk : w.baseHom = k) (hk : k ≫ g = g')
    (hwπ : w ≫ X₀.pullbackAlongπ g = X₀.pullbackAlongπ g')
    (h : { h : T ⟶ d₀.Z // h ≫ d₀.f = g }) :
    P.map w.op (d₀.eqv g h) =
      d₀.eqv g' ⟨k ≫ h.1, by rw [Category.assoc, h.2, hk]⟩ := by
  subst hk
  have hw : w = X₀.pullbackAlongMap g k := by
    apply (EllObj.homPullbackAlongEquiv X₀ g (X₀.pullbackAlong (k ≫ g))).injective
    refine Subtype.ext (Prod.ext ?_ ?_)
    · show w ≫ X₀.pullbackAlongπ g = X₀.pullbackAlongMap g k ≫ X₀.pullbackAlongπ g
      rw [hwπ, pullbackAlongMap_pullbackAlongπ']
    · exact hbk
  rw [hw]
  exact (d₀.nat g k h).symm

/-! ### Shared δ-torsor infrastructure for the B3 bijection (KM pp. 114–116)

VERIFIED setup (fable-P4 analysis): the classifying map and its base map typecheck; the torsor
field `td.torsor` IS `IsIso (torsorCompare td.f td.σZ td.over_base)` (defeq), and `Flat`/
`QuasiCompact` synthesise on `td.f` from `td.etale`/`td.finite`. The remaining gaps are the
equivariance of the classifying base map, the Ell/R-level descent of `v`, and the two final
`P.map`-identities. -/

/-- The classifying-map base for a `P`-class `α` over the δ-torsor of `Y`:
`fb : td.Z ⟶ XM.base`, the base map of `homEquiv.symm ⟨α_td, β_univ⟩`. -/
noncomputable def bijClassBase {P Q : ModuliProblem R} {G : Type u} [Group G] [Finite G]
    {φ : G →* Aut Q} (cd : CoreData P Q φ) {Y : EllObj R} (td : TorsorData φ Y)
    (α : P.obj (op Y)) : td.Z ⟶ cd.XM.base :=
  (cd.rM.homEquiv.symm ⟨P.map (Y.pullbackAlongπ td.f).op α,
    td.eqv td.f ⟨𝟙 td.Z, Category.id_comp td.f⟩⟩).baseHom

/-- **G-equivariance of the classifying morphism** (the δ-classifying map is G-equivariant,
KM p. 115). The deck transformation `σZ.hom γ` of the δ-torsor precomposes into the classifying
morphism as postcomposition by `(A γ⁻¹).hom` on `XM`, where `A δ = rM.autMulHom (simulAutSnd (φ δ))`
(the `γ⁻¹` is the [B2-TD-CONV] convention of `TorsorData.equivariant`). The
`q.baseHom`-invariance of the descent then follows (over all `γ`) from `cd.hqinv`. -/
private theorem homToPullbackAlong_classifying_comm
    {P Q : ModuliProblem R} {G : Type u} [Group G] [Finite G]
    {φ : G →* Aut Q} (cd : CoreData P Q φ) {Y : EllObj R} (td : TorsorData φ Y)
    (α : P.obj (op Y)) (γ : G) :
    EllObj.homToPullbackAlong (Y.pullbackAlongπ td.f) (td.σZ.hom γ) (td.over_base γ) ≫
        cd.rM.homEquiv.symm (P.map (Y.pullbackAlongπ td.f).op α,
          td.eqv td.f ⟨𝟙 td.Z, Category.id_comp td.f⟩) =
      cd.rM.homEquiv.symm (P.map (Y.pullbackAlongπ td.f).op α,
          td.eqv td.f ⟨𝟙 td.Z, Category.id_comp td.f⟩) ≫
        (cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ⁻¹))).hom := by
  set β : Q.obj (op (Y.pullbackAlong td.f)) :=
    td.eqv td.f ⟨𝟙 td.Z, Category.id_comp td.f⟩ with hβ
  set ρ : Y.pullbackAlong td.f ⟶ Y.pullbackAlong td.f :=
    EllObj.homToPullbackAlong (Y.pullbackAlongπ td.f) (td.σZ.hom γ) (td.over_base γ) with hρ
  set c : Y.pullbackAlong td.f ⟶ cd.XM :=
    cd.rM.homEquiv.symm (P.map (Y.pullbackAlongπ td.f).op α, β) with hc
  have hHEc : cd.rM.homEquiv c = (P.map (Y.pullbackAlongπ td.f).op α, β) := by
    rw [hc]; exact Equiv.apply_symm_apply _ _
  apply cd.rM.homEquiv.injective
  rw [cd.rM.homEquiv_comp, hHEc,
    show (cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ⁻¹))).hom
        = cd.rM.transportHom ((P.simulAutSnd Q) (φ γ⁻¹)).hom from rfl,
    cd.rM.homEquiv_comp_transportHom, hHEc]
  refine Prod.ext ?_ ?_
  · show P.map ρ.op (P.map (Y.pullbackAlongπ td.f).op α)
        = P.map (Y.pullbackAlongπ td.f).op α
    rw [← Functor.map_comp_apply, ← op_comp, hρ,
      EllObj.homToPullbackAlong_pullbackAlongπ]
  · show Q.map ρ.op β = (φ γ⁻¹).hom.app (op (Y.pullbackAlong td.f)) β
    rw [hρ, hβ, map_eqv' td.toRelRepData
      (EllObj.homToPullbackAlong (Y.pullbackAlongπ td.f) (td.σZ.hom γ) (td.over_base γ))
      (td.σZ.hom γ) (EllObj.homToPullbackAlong_baseHom _ _ _) (td.over_base γ)
      (EllObj.homToPullbackAlong_pullbackAlongπ _ _ _) ⟨𝟙 td.Z, Category.id_comp td.f⟩]
    exact Eq.trans (congrArg (td.eqv td.f) (Subtype.ext
        (show td.σZ.hom γ ≫ 𝟙 td.Z = 𝟙 td.Z ≫ td.σZ.hom γ by
          rw [Category.comp_id, Category.id_comp])))
      (td.equivariant td.f ⟨𝟙 td.Z, Category.id_comp td.f⟩ γ)

/-- **Curve-level `q`-invariance re-derived from `CoreData`** (rigidity + θ-tautology, KM p. 113).
`CoreData` only exposes the base-level `hqinv`; the full Ell/R-level invariance
`(A γ).inv ≫ q = q` (needed to descend the curve) follows because the connecting automorphism
`ξ` between `(A γ).inv ≫ q` and `q` (equal base maps by `hqinv`) fixes the universal `P`-value
(`hα₀` + the θ-tautology `map_inv_autMulHom_fst`), so rigidity forces `ξ = 𝟙`. -/
private theorem coreData_qinv_full {P Q : ModuliProblem R} {G : Type u} [Group G] [Finite G]
    {φ : G →* Aut Q} (cd : CoreData P Q φ) (hrig : P.Rigid) (γ : G) :
    (cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ))).inv ≫ cd.q = cd.q := by
  set A := cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ)) with hA
  have hb : (A.inv ≫ cd.q).baseHom = cd.q.baseHom := cd.hqinv γ
  set ξ := EllObj.connectHom (A.inv ≫ cd.q) cd.q hb with hξ
  set ξ' := EllObj.connectHom cd.q (A.inv ≫ cd.q) hb.symm with hξ'
  have hξw : ξ ≫ cd.q = A.inv ≫ cd.q := EllObj.connectHom_comp _ _ hb
  have hξ'w : ξ' ≫ (A.inv ≫ cd.q) = cd.q := EllObj.connectHom_comp _ _ hb.symm
  have hii : ξ ≫ ξ' = 𝟙 cd.XM := by
    refine EllObj.eq_id_of_baseHom_of_comp (A.inv ≫ cd.q) _ ?_ ?_
    · rw [show (ξ ≫ ξ').baseHom = ξ.baseHom ≫ ξ'.baseHom from rfl,
        EllObj.connectHom_baseHom, EllObj.connectHom_baseHom, Category.id_comp]
    · rw [Category.assoc, hξ'w, hξw]
  have hii' : ξ' ≫ ξ = 𝟙 cd.XM := by
    refine EllObj.eq_id_of_baseHom_of_comp cd.q _ ?_ ?_
    · rw [show (ξ' ≫ ξ).baseHom = ξ'.baseHom ≫ ξ.baseHom from rfl,
        EllObj.connectHom_baseHom, EllObj.connectHom_baseHom, Category.id_comp]
    · rw [Category.assoc, hξw, hξ'w]
  have hfix : P.map ξ.op (cd.rM.homEquiv (𝟙 cd.XM)).1 = (cd.rM.homEquiv (𝟙 cd.XM)).1 := by
    rw [← cd.hα₀, ← Functor.map_comp_apply, ← op_comp, hξw, op_comp, Functor.map_comp_apply,
      cd.hα₀]
    exact map_inv_autMulHom_fst P Q φ cd.rM γ
  have hξid : ξ = 𝟙 cd.XM := by
    by_contra hne
    exact hrig cd.XM ⟨ξ, ξ', hii, hii'⟩ (EllObj.connectHom_baseHom _ _ hb)
      (fun hrefl => hne (congrArg Iso.hom hrefl)) (cd.rM.homEquiv (𝟙 cd.XM)).1 hfix
  rw [← hξw, hξid, Category.id_comp]

/-- **Descent of a `G`-deck-invariant `Ell/R`-morphism along the δ-torsor** (KM p. 115). A morphism
`g : Y.pullbackAlong td.f ⟶ X` invariant under the deck action `ρ γ` descends through the torsor
projection `π_td = Y.pullbackAlongπ td.f`: the base map descends by `existsUnique_descent_of_torsor`,
the curve top by the same on the fppf curve-torsor `pullback.snd td.f Y.curve.π` (base change of `td.f`,
`isIso_torsorCompare_pullback`), and `base_w`/`zero_w` by `td.f` being an epimorphism.

VERIFIED here except the cartesian square `IsPullback vtop Y.curve.π X.curve.π f₀`, which is the
fppf descent of `g.isPullback` along `td.f` (the comparison `Y.curve.E ⟶ X.curve.E ×_{X.base} Y.base`
is an iso by `isIso_of_isPullback_of_fppf`, its base change along `td.f` being `g.top` via the
`pullbackRightPullbackFstIso` pasting and `g.isPullback.isoPullback`). -/
private theorem descend_deckInvariant {Q : ModuliProblem R} {G : Type u} [Group G] [Finite G]
    {φ : G →* Aut Q} {Y : EllObj R} (td : TorsorData φ Y)
    [Surjective td.f] [Flat td.f] [QuasiCompact td.f] {X : EllObj R}
    (g : Y.pullbackAlong td.f ⟶ X)
    (hg : ∀ γ, EllObj.homToPullbackAlong (Y.pullbackAlongπ td.f) (td.σZ.hom γ) (td.over_base γ) ≫ g
      = g) :
    ∃ v : Y ⟶ X, Y.pullbackAlongπ td.f ≫ v = g := by
  haveI : Epi td.f := AlgebraicGeometry.Flat.epi_of_flat_of_surjective td.f
  -- pin the deck endomorphism's type so its `.top`/`.isPullback` are well-formed
  let ρ : G → (Y.pullbackAlong td.f ⟶ Y.pullbackAlong td.f) :=
    fun γ => EllObj.homToPullbackAlong (Y.pullbackAlongπ td.f) (td.σZ.hom γ) (td.over_base γ)
  have hρg : ∀ γ, ρ γ ≫ g = g := hg
  have hρπ : ∀ γ, ρ γ ≫ Y.pullbackAlongπ td.f = Y.pullbackAlongπ td.f :=
    fun γ => EllObj.homToPullbackAlong_pullbackAlongπ _ _ _
  -- (a) descend the base map
  have hgb : ∀ γ, td.σZ.hom γ ≫ g.baseHom = g.baseHom :=
    fun γ => congrArg EllHom.baseHom (hρg γ)
  obtain ⟨f₀, hf₀, -⟩ :=
    existsUnique_descent_of_torsor td.σZ td.over_base td.torsor g.baseHom hgb
  -- (b) descend the curve top along the fppf curve-torsor `pullback.snd td.f Y.curve.π`
  haveI : Surjective (pullback.snd td.f Y.curve.π) :=
    MorphismProperty.pullback_snd _ _ ‹Surjective td.f›
  haveI : Flat (pullback.snd td.f Y.curve.π) := MorphismProperty.pullback_snd _ _ ‹Flat td.f›
  haveI : QuasiCompact (pullback.snd td.f Y.curve.π) :=
    MorphismProperty.pullback_snd _ _ ‹QuasiCompact td.f›
  -- the curve deck action, typed as an endomorphism of `pullback Y.curve.π td.f`
  let τ : G → (pullback Y.curve.π td.f ⟶ pullback Y.curve.π td.f) := fun γ => (ρ γ).top
  have hτg : ∀ γ, τ γ ≫ g.top = g.top := fun γ => congrArg EllHom.top (hρg γ)
  have hmap : ∀ γ, (pullbackTorsorAction td.σZ td.over_base Y.curve.π).hom γ ≫
      pullback.fst td.f Y.curve.π = pullback.fst td.f Y.curve.π ≫ td.σZ.hom γ := by
    intro γ; rw [pullbackTorsorAction_hom]; simp [pullback.map, pullback.lift_fst]
  have hcomm : ∀ γ, (pullbackTorsorAction td.σZ td.over_base Y.curve.π).hom γ ≫
        (pullbackSymmetry td.f Y.curve.π).hom =
      (pullbackSymmetry td.f Y.curve.π).hom ≫ τ γ := by
    intro γ
    have hρfst : τ γ ≫ pullback.fst Y.curve.π td.f = pullback.fst Y.curve.π td.f :=
      congrArg EllHom.top (hρπ γ)
    have hρsnd : τ γ ≫ pullback.snd Y.curve.π td.f =
        pullback.snd Y.curve.π td.f ≫ td.σZ.hom γ := (ρ γ).isPullback.w
    apply pullback.hom_ext
    · rw [Category.assoc, pullbackSymmetry_hom_comp_fst, pullbackTorsorAction_over,
        Category.assoc, hρfst, pullbackSymmetry_hom_comp_fst]
    · rw [Category.assoc, pullbackSymmetry_hom_comp_snd, Category.assoc, hρsnd, ← Category.assoc,
        pullbackSymmetry_hom_comp_snd]
      exact hmap γ
  have hinv_curve : ∀ γ, (pullbackTorsorAction td.σZ td.over_base Y.curve.π).hom γ ≫
      ((pullbackSymmetry td.f Y.curve.π).hom ≫ g.top) =
      (pullbackSymmetry td.f Y.curve.π).hom ≫ g.top := by
    intro γ
    rw [← Category.assoc, hcomm γ, Category.assoc, hτg γ]
  obtain ⟨vtop, hvtop_raw, -⟩ :=
    existsUnique_descent_of_torsor (pullbackTorsorAction td.σZ td.over_base Y.curve.π)
      (pullbackTorsorAction_over td.σZ td.over_base Y.curve.π)
      (isIso_torsorCompare_pullback td.σZ td.over_base td.torsor Y.curve.π)
      ((pullbackSymmetry td.f Y.curve.π).hom ≫ g.top) hinv_curve
  have hvtop : (Y.pullbackAlongπ td.f).top ≫ vtop = g.top := by
    have h := hvtop_raw
    rw [← pullbackSymmetry_hom_comp_fst td.f Y.curve.π, Category.assoc] at h
    exact (cancel_epi (pullbackSymmetry td.f Y.curve.π).hom).mp h
  -- (c) `base_w`/`zero_w` by `td.f`-epi; the cartesian square is the fppf descent of `g.isPullback`.
  have hbw : f₀ ≫ X.structMap = Y.structMap := by
    refine (cancel_epi td.f).mp ?_
    rw [← Category.assoc, hf₀]; exact g.base_w
  have hz0 : (Y.pullbackAlong td.f).curve.zero ≫ (Y.pullbackAlongπ td.f).top =
      td.f ≫ Y.curve.zero := (Y.pullbackAlongπ td.f).zero_w
  have hzero : Y.curve.zero ≫ vtop = f₀ ≫ X.curve.zero := by
    refine (cancel_epi td.f).mp ?_
    rw [← Category.assoc, ← Category.assoc, hf₀]
    exact (congrArg (· ≫ vtop) hz0.symm).trans ((Category.assoc _ _ _).trans
      ((congrArg ((Y.pullbackAlong td.f).curve.zero ≫ ·) hvtop).trans g.zero_w))
  -- the curve cartesian square is the fppf descent of `g.isPullback` along `td.f`.
  have hvtop' : pullback.fst Y.curve.π td.f ≫ vtop = g.top := hvtop
  have hbc : IsPullback (pullback.fst Y.curve.π td.f ≫ vtop) (pullback.snd Y.curve.π td.f)
      X.curve.π (td.f ≫ f₀) := by
    rw [hvtop', hf₀]; exact g.isPullback
  have hw : vtop ≫ X.curve.π = Y.curve.π ≫ f₀ := by
    refine (cancel_epi (pullback.fst Y.curve.π td.f)).mp ?_
    rw [reassoc_of% hvtop', reassoc_of% pullback.condition, hf₀]
    exact g.isPullback.w
  have hsq : IsPullback vtop Y.curve.π X.curve.π f₀ :=
    isPullback_of_fppf_baseChange hw td.f hbc
  exact ⟨{ baseHom := f₀, base_w := hbw, top := vtop, isPullback := hsq, zero_w := hzero },
    EllHom.ext hf₀ hvtop⟩

/-- **fppf-separatedness of a relatively representable `P` along the torsor cover** (KM 4.1;
`moduliProblem_fppf_separated`, `Moduli/Stack.lean`): restriction of `P`-values along the fppf
projection `Y.pullbackAlongπ f` (for `f` flat + locally of finite presentation + surjective) is
injective. (Re-stated here because `Stack.lean` is transitively unimportable through an unrelated
`GammaH` breakage; the proof is the classifying-section `cancel_epi` of `moduliProblem_fppf_separated`
composed with the identity-chart iso `Y ≅ Y.pullbackAlong (𝟙 Y.base)`.) -/
private theorem P_pullbackAlongπ_inj {P : ModuliProblem R} (hPrr : P.RelativelyRepresentable)
    {Y : EllObj R} {Z : Scheme.{u}} (f : Z ⟶ Y.base)
    [Flat f] [LocallyOfFinitePresentation f] [Surjective f]
    {a b : P.obj (op Y)}
    (hab : P.map (Y.pullbackAlongπ f).op a = P.map (Y.pullbackAlongπ f).op b) : a = b := by
  haveI : Epi f := AlgebraicGeometry.Flat.epi_of_flat_of_surjective f
  obtain ⟨d⟩ := (relativelyRepresentable_iff_nonempty_relRepData P).mp hPrr Y
  -- comparison `w = π_f ≫ (Y ≅ Y.pullbackAlong 𝟙)` from the identity chart, lying over `f`
  have hmid : (EllObj.isoPullbackAlong (𝟙 Y)).hom ≫ Y.pullbackAlongπ (𝟙 Y.base) = 𝟙 Y :=
    EllObj.toPullbackAlong_pullbackAlongπ (𝟙 Y)
  have hwπ : (Y.pullbackAlongπ f ≫ (EllObj.isoPullbackAlong (𝟙 Y)).hom) ≫
      Y.pullbackAlongπ (𝟙 Y.base) = Y.pullbackAlongπ f := by
    rw [Category.assoc, hmid, Category.comp_id]
  -- each `P`-value over `Y`, restricted along `π_f`, is the chart-`f` value of `f ≫ (its
  -- identity-chart classifying section)` (`map_eqv'` handles the `k ≫ g` bookkeeping)
  have hae : ∀ c : P.obj (op Y), P.map (Y.pullbackAlongπ f).op c =
      d.eqv f ⟨f ≫ ((d.eqv (𝟙 Y.base)).symm
          (P.map (EllObj.isoPullbackAlong (𝟙 Y)).inv.op c)).1,
        by rw [Category.assoc, ((d.eqv (𝟙 Y.base)).symm
          (P.map (EllObj.isoPullbackAlong (𝟙 Y)).inv.op c)).2, Category.comp_id]⟩ := by
    intro c
    have hc : c = P.map (EllObj.isoPullbackAlong (𝟙 Y)).hom.op (d.eqv (𝟙 Y.base)
        ((d.eqv (𝟙 Y.base)).symm (P.map (EllObj.isoPullbackAlong (𝟙 Y)).inv.op c))) := by
      rw [Equiv.apply_symm_apply, ← Functor.map_comp_apply, ← op_comp, Iso.hom_inv_id, op_id,
        Functor.map_id_apply]
    conv_lhs => rw [hc, ← Functor.map_comp_apply, ← op_comp]
    exact map_eqv' d (Y.pullbackAlongπ f ≫ (EllObj.isoPullbackAlong (𝟙 Y)).hom) f
      (by show f ≫ 𝟙 Y.base = f; exact Category.comp_id f)
      (Category.comp_id f) hwπ _
  rw [hae a, hae b] at hab
  have hfeq : f ≫ ((d.eqv (𝟙 Y.base)).symm
        (P.map (EllObj.isoPullbackAlong (𝟙 Y)).inv.op a)).1 =
      f ≫ ((d.eqv (𝟙 Y.base)).symm
        (P.map (EllObj.isoPullbackAlong (𝟙 Y)).inv.op b)).1 :=
    congrArg Subtype.val ((d.eqv f).injective hab)
  have hsec : (d.eqv (𝟙 Y.base)).symm (P.map (EllObj.isoPullbackAlong (𝟙 Y)).inv.op a) =
      (d.eqv (𝟙 Y.base)).symm (P.map (EllObj.isoPullbackAlong (𝟙 Y)).inv.op b) :=
    Subtype.ext ((cancel_epi f).mp hfeq)
  have hval : P.map (EllObj.isoPullbackAlong (𝟙 Y)).inv.op a =
      P.map (EllObj.isoPullbackAlong (𝟙 Y)).inv.op b := by
    have hh := congrArg (d.eqv (𝟙 Y.base)) hsec
    rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hh
  have hfin := congrArg (P.map (EllObj.isoPullbackAlong (𝟙 Y)).hom.op) hval
  rwa [← Functor.map_comp_apply, ← op_comp, Iso.hom_inv_id, op_id, Functor.map_id_apply,
    ← Functor.map_comp_apply, ← op_comp, Iso.hom_inv_id, op_id, Functor.map_id_apply] at hfin

/-- [B3-bij existence a — KM p. 115] curve-iso descent along the δ-torsor (rigidity). -/
theorem coreData_surjective (P Q : ModuliProblem R) {G : Type u} [Group G] [Finite G]
    (φ : G →* Aut Q) (htors : ∀ X : EllObj R, Nonempty (TorsorData φ X)) (hrig : P.Rigid)
    (hPrr : P.RelativelyRepresentable) (cd : CoreData P Q φ) (Y : EllObj R)
    (α : P.obj (op Y)) : ∃ v : Y ⟶ cd.X₀, P.map v.op cd.α₀ = α := by
  classical
  obtain ⟨td⟩ := htors Y
  haveI := td.surjective; haveI := td.etale; haveI := td.finite
  haveI : Flat td.f := inferInstance
  haveI : QuasiCompact td.f := inferInstance
  have htorsZ : IsIso (torsorCompare td.f td.σZ td.over_base) := td.torsor
  set fb : td.Z ⟶ cd.XM.base := bijClassBase cd td α with hfb
  -- (i)+(ii) descend `fb ≫ q.baseHom` (invariant) through `td.f` to `f₀ : Y.base ⟶ X₀.base`.
  -- Equivariance: `σZ.hom γ ≫ fb = fb ≫ (A γ).hom.baseHom` (ofAut inverts, so `(A γ).hom.baseHom`
  -- is the moduli action `σ.hom γ⁻¹`); then `q.baseHom`-invariance follows from `cd.hqinv`.
  have hinv : ∀ γ, td.σZ.hom γ ≫ (fb ≫ cd.q.baseHom) = fb ≫ cd.q.baseHom := by
    intro γ
    have hbase : td.σZ.hom γ ≫ fb =
        fb ≫ (cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ⁻¹))).hom.baseHom :=
      congrArg EllHom.baseHom (homToPullbackAlong_classifying_comm cd td α γ)
    have h1 : (cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ⁻¹))).inv.baseHom ≫ cd.q.baseHom
        = cd.q.baseHom := cd.hqinv γ⁻¹
    have hAinv : (cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ⁻¹))).hom.baseHom ≫
        (cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ⁻¹))).inv.baseHom = 𝟙 cd.XM.base :=
      congrArg EllHom.baseHom (cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ⁻¹))).hom_inv_id
    have hq' : (cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ⁻¹))).hom.baseHom ≫ cd.q.baseHom
        = cd.q.baseHom := by
      calc (cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ⁻¹))).hom.baseHom ≫ cd.q.baseHom
          = (cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ⁻¹))).hom.baseHom ≫
              ((cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ⁻¹))).inv.baseHom ≫ cd.q.baseHom) := by
            rw [h1]
        _ = ((cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ⁻¹))).hom.baseHom ≫
              (cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ⁻¹))).inv.baseHom) ≫ cd.q.baseHom := by
            rw [Category.assoc]
        _ = 𝟙 cd.XM.base ≫ cd.q.baseHom := by rw [hAinv]
        _ = cd.q.baseHom := Category.id_comp _
    rw [← Category.assoc, hbase, Category.assoc, hq']
  obtain ⟨f₀, hf₀, -⟩ :=
    existsUnique_descent_of_torsor td.σZ td.over_base htorsZ (fb ≫ cd.q.baseHom) hinv
  -- The classifying Ell/R-morphism `f_ell` (base map `fb`), and `g := f_ell ≫ q`.
  set f_ell : Y.pullbackAlong td.f ⟶ cd.XM :=
    cd.rM.homEquiv.symm (P.map (Y.pullbackAlongπ td.f).op α,
      td.eqv td.f ⟨𝟙 td.Z, Category.id_comp td.f⟩) with hf_ell
  -- Curve-level `q`-invariance: `(A γ).hom ≫ q = q` at the full Ell/R level (from `coreData_qinv_full`).
  have hAq : ∀ γ, (cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ))).hom ≫ cd.q = cd.q := by
    intro γ
    have hqi := coreData_qinv_full cd hrig γ
    calc (cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ))).hom ≫ cd.q
        = (cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ))).hom ≫
            ((cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ))).inv ≫ cd.q) := by rw [hqi]
      _ = ((cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ))).hom ≫
            (cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ))).inv) ≫ cd.q := by rw [Category.assoc]
      _ = 𝟙 cd.XM ≫ cd.q := by rw [(cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ))).hom_inv_id]
      _ = cd.q := Category.id_comp _
  -- `g := f_ell ≫ q` is `G`-deck-invariant at the full Ell/R level (`ρ γ ≫ g = g`), so it
  -- descends through the torsor projection `π_td` to the required `v : Y ⟶ X₀`.
  have hg_inv : ∀ γ,
      EllObj.homToPullbackAlong (Y.pullbackAlongπ td.f) (td.σZ.hom γ) (td.over_base γ) ≫
        (f_ell ≫ cd.q) = f_ell ≫ cd.q := by
    intro γ
    rw [hf_ell, ← Category.assoc, homToPullbackAlong_classifying_comm cd td α γ,
      Category.assoc, hAq γ⁻¹]
  -- Descend the deck-invariant `g = f_ell ≫ q` through `π_td` to `v : Y ⟶ cd.X₀`.
  obtain ⟨v, hv⟩ := descend_deckInvariant td (f_ell ≫ cd.q) hg_inv
  refine ⟨v, ?_⟩
  -- `P.map v.op α₀ = α`: pull back along the fppf cover `π_td` — both sides then agree.
  have key : P.map (Y.pullbackAlongπ td.f).op (P.map v.op cd.α₀) =
      P.map (Y.pullbackAlongπ td.f).op α := by
    have e1 : P.map (Y.pullbackAlongπ td.f).op (P.map v.op cd.α₀) =
        P.map (f_ell ≫ cd.q).op cd.α₀ := by
      rw [← Functor.map_comp_apply, ← op_comp, hv]
    have hHE : cd.rM.homEquiv f_ell = (P.simul Q).map f_ell.op (cd.rM.homEquiv (𝟙 cd.XM)) := by
      conv_lhs => rw [← Category.comp_id f_ell]
      exact cd.rM.homEquiv_comp f_ell (𝟙 cd.XM)
    have e2 : P.map (f_ell ≫ cd.q).op cd.α₀ = (cd.rM.homEquiv f_ell).1 := by
      rw [op_comp, Functor.map_comp_apply, cd.hα₀]
      exact (congrArg Prod.fst hHE).symm
    have e3 : (cd.rM.homEquiv f_ell).1 = P.map (Y.pullbackAlongπ td.f).op α := by
      rw [hf_ell, Equiv.apply_symm_apply]
    rw [e1, e2, e3]
  -- cancel the fppf restriction `P.map π_td.op` (relatively-representable ⟹ fppf-separated)
  haveI : Flat td.f := inferInstance
  haveI : LocallyOfFinitePresentation td.f := inferInstance
  exact P_pullbackAlongπ_inj hPrr td.f key

/-- **Equal base maps ⟹ equal (rigidity)**: two `Ell/R`-morphisms `v, v' : Y ⟶ X₀` with the same
base map and inducing the same `P`-class agree. The connecting automorphism `ξ` (over the identity
base) fixes the `P`-value `P.map v'.op α₀`, so rigidity forces `ξ = 𝟙`, hence `v = ξ ≫ v' = v'`.
This is the second half of the KM p. 116 uniqueness argument. -/
private theorem coreData_hom_eq_of_baseHom_eq {P Q : ModuliProblem R} {G : Type u} [Group G]
    [Finite G] {φ : G →* Aut Q} (cd : CoreData P Q φ) (hrig : P.Rigid) {Y : EllObj R}
    (v v' : Y ⟶ cd.X₀) (hbb : v.baseHom = v'.baseHom)
    (h : P.map v.op cd.α₀ = P.map v'.op cd.α₀) : v = v' := by
  set ξ := EllObj.connectHom v v' hbb with hξ
  set ξ' := EllObj.connectHom v' v hbb.symm with hξ'
  have hξw : ξ ≫ v' = v := EllObj.connectHom_comp _ _ hbb
  have hξ'w : ξ' ≫ v = v' := EllObj.connectHom_comp _ _ hbb.symm
  have hii : ξ ≫ ξ' = 𝟙 Y := by
    refine EllObj.eq_id_of_baseHom_of_comp v _ ?_ ?_
    · rw [show (ξ ≫ ξ').baseHom = ξ.baseHom ≫ ξ'.baseHom from rfl,
        EllObj.connectHom_baseHom, EllObj.connectHom_baseHom, Category.id_comp]
    · rw [Category.assoc, hξ'w, hξw]
  have hii' : ξ' ≫ ξ = 𝟙 Y := by
    refine EllObj.eq_id_of_baseHom_of_comp v' _ ?_ ?_
    · rw [show (ξ' ≫ ξ).baseHom = ξ'.baseHom ≫ ξ.baseHom from rfl,
        EllObj.connectHom_baseHom, EllObj.connectHom_baseHom, Category.id_comp]
    · rw [Category.assoc, hξw, hξ'w]
  have hfix : P.map ξ.op (P.map v'.op cd.α₀) = P.map v'.op cd.α₀ := by
    rw [← Functor.map_comp_apply, ← op_comp, hξw, h]
  have hξid : ξ = 𝟙 Y := by
    by_contra hne
    exact hrig Y ⟨ξ, ξ', hii, hii'⟩ (EllObj.connectHom_baseHom _ _ hbb)
      (fun hrefl => hne (congrArg Iso.hom hrefl)) (P.map v'.op cd.α₀) hfix
  rw [← hξw, hξid, Category.id_comp]

private theorem coreData_key (P Q : ModuliProblem R) {G : Type u} [Group G] [Finite G]
    (φ : G →* Aut Q) (cd : CoreData P Q φ) {Y : EllObj R} (td : TorsorData φ Y) (v : Y ⟶ cd.X₀)
    [Flat cd.q.baseHom] [Surjective cd.q.baseHom] :
    td.f ≫ v.baseHom = bijClassBase cd td (P.map v.op cd.α₀) ≫ cd.q.baseHom := by
  classical
  haveI := td.surjective; haveI := td.etale; haveI := td.finite
  haveI : Flat td.f := inferInstance
  haveI : QuasiCompact td.f := inferInstance
  set α : P.obj (op Y) := P.map v.op cd.α₀ with hα
  -- the pulled-back G-torsor of `v` along the universal quotient `cd.q.baseHom`
  set Pv := Limits.pullback cd.q.baseHom v.baseHom with hPv
  set fstv : Pv ⟶ cd.XM.base := pullback.fst cd.q.baseHom v.baseHom with hfstv
  set sndv : Pv ⟶ Y.base := pullback.snd cd.q.baseHom v.baseHom with hsndv
  have hcond : fstv ≫ cd.q.baseHom = sndv ≫ v.baseHom := pullback.condition
  -- the classifying morphism `f_ell` over the δ-torsor chart (base map = `bijClassBase`)
  set fell : Y.pullbackAlong td.f ⟶ cd.XM :=
    cd.rM.homEquiv.symm (P.map (Y.pullbackAlongπ td.f).op α,
      td.eqv td.f ⟨𝟙 td.Z, Category.id_comp td.f⟩) with hfell
  have hbij : bijClassBase cd td α = fell.baseHom := rfl
  -- the inverse cartesian comparison collapses to the chart projection
  have hqiso : (EllObj.isoPullbackAlong cd.q).inv ≫ cd.q =
      cd.X₀.pullbackAlongπ cd.q.baseHom := by
    rw [Iso.inv_comp_eq]; exact (EllObj.toPullbackAlong_pullbackAlongπ cd.q).symm
  -- the lift `μv` of `π_sndv ≫ v` through the quotient `cd.q`, over the `Pv`-chart
  have hh : fstv ≫ cd.q.baseHom = (Y.pullbackAlongπ sndv ≫ v).baseHom := hcond
  set muv : Y.pullbackAlong sndv ⟶ cd.XM :=
    EllObj.homToPullbackAlong (Y.pullbackAlongπ sndv ≫ v) fstv hh ≫
      (EllObj.isoPullbackAlong cd.q).inv with hmuv
  have hmuvb : muv.baseHom = fstv := by
    rw [hmuv]
    show fstv ≫ (EllObj.isoPullbackAlong cd.q).inv.baseHom = fstv
    rw [show (EllObj.isoPullbackAlong cd.q).inv.baseHom = 𝟙 cd.XM.base from rfl,
      Category.comp_id]
  have hmuvq : muv ≫ cd.q = Y.pullbackAlongπ sndv ≫ v := by
    rw [hmuv, Category.assoc, hqiso, EllObj.homToPullbackAlong_pullbackAlongπ]
  -- the P-value of `μv`
  have hPval : (cd.rM.homEquiv muv).1 = P.map (Y.pullbackAlongπ sndv).op α := by
    have hHE : cd.rM.homEquiv muv = (P.simul Q).map muv.op (cd.rM.homEquiv (𝟙 cd.XM)) := by
      conv_lhs => rw [← Category.comp_id muv]
      exact cd.rM.homEquiv_comp muv (𝟙 cd.XM)
    have hP1 : (cd.rM.homEquiv muv).1 = P.map muv.op (cd.rM.homEquiv (𝟙 cd.XM)).1 :=
      congrArg Prod.fst hHE
    rw [hP1, ← cd.hα₀, ← Functor.map_comp_apply, ← op_comp, hmuvq, op_comp,
      Functor.map_comp_apply, hα]
  -- the δ-value of `μv`, classified into the δ-torsor `td.Z`
  set dv : Q.obj (op (Y.pullbackAlong sndv)) := (cd.rM.homEquiv muv).2 with hdv
  set θv : Pv ⟶ td.Z := ((td.eqv sndv).symm dv).1 with hθv
  have hθf : θv ≫ td.f = sndv := ((td.eqv sndv).symm dv).2
  have hθeqv : td.eqv sndv ⟨θv, hθf⟩ = dv := (td.eqv sndv).apply_symm_apply dv
  -- the chart comparison over `θv`
  set θtil : Y.pullbackAlong sndv ⟶ Y.pullbackAlong td.f :=
    EllObj.homToPullbackAlong (Y.pullbackAlongπ sndv) θv hθf with hθtil
  have hθtilπ : θtil ≫ Y.pullbackAlongπ td.f = Y.pullbackAlongπ sndv :=
    EllObj.homToPullbackAlong_pullbackAlongπ _ _ _
  have hfellHE : cd.rM.homEquiv fell = (P.map (Y.pullbackAlongπ td.f).op α,
      td.eqv td.f ⟨𝟙 td.Z, Category.id_comp td.f⟩) := by
    rw [hfell]; exact cd.rM.homEquiv.apply_symm_apply _
  -- KEY classifier identity: `μv = θtil ≫ f_ell`
  have hmuv_eq : muv = θtil ≫ fell := by
    apply cd.rM.homEquiv.injective
    rw [cd.rM.homEquiv_comp θtil fell, hfellHE]
    refine Prod.ext ?_ ?_
    · show (cd.rM.homEquiv muv).1 = P.map θtil.op (P.map (Y.pullbackAlongπ td.f).op α)
      rw [hPval]
      conv_rhs => rw [← Functor.map_comp_apply, ← op_comp, hθtilπ]
    · show (cd.rM.homEquiv muv).2 = Q.map θtil.op (td.eqv td.f ⟨𝟙 td.Z, Category.id_comp td.f⟩)
      rw [← hdv, ← hθeqv, hθtil,
        map_eqv' td.toRelRepData _ θv (EllObj.homToPullbackAlong_baseHom _ _ _) hθf
          (EllObj.homToPullbackAlong_pullbackAlongπ _ _ _) ⟨𝟙 td.Z, Category.id_comp td.f⟩]
      exact congrArg (td.eqv sndv) (Subtype.ext (Category.comp_id θv).symm)
  -- (I): `fstv = θv ≫ bijClassBase`
  have hI : fstv = θv ≫ fell.baseHom := by
    have hb := congrArg EllHom.baseHom hmuv_eq
    rw [hmuvb] at hb
    rw [hb]
    show θtil.baseHom ≫ fell.baseHom = θv ≫ fell.baseHom
    rfl
  -- G-invariance of `fell.baseHom ≫ q.base`, from equivariance of the classifier + hqinv
  have hinv : ∀ γ, td.σZ.hom γ ≫ (fell.baseHom ≫ cd.q.baseHom) =
      fell.baseHom ≫ cd.q.baseHom := by
    intro γ
    have hbase : td.σZ.hom γ ≫ fell.baseHom =
        fell.baseHom ≫ (cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ⁻¹))).hom.baseHom :=
      congrArg EllHom.baseHom (homToPullbackAlong_classifying_comm cd td α γ)
    have h1 : (cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ⁻¹))).inv.baseHom ≫ cd.q.baseHom
        = cd.q.baseHom := cd.hqinv γ⁻¹
    have hAinv : (cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ⁻¹))).hom.baseHom ≫
        (cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ⁻¹))).inv.baseHom = 𝟙 cd.XM.base :=
      congrArg EllHom.baseHom (cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ⁻¹))).hom_inv_id
    have hq' : (cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ⁻¹))).hom.baseHom ≫ cd.q.baseHom
        = cd.q.baseHom := by
      calc (cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ⁻¹))).hom.baseHom ≫ cd.q.baseHom
          = (cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ⁻¹))).hom.baseHom ≫
              ((cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ⁻¹))).inv.baseHom ≫ cd.q.baseHom) := by
            rw [h1]
        _ = ((cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ⁻¹))).hom.baseHom ≫
              (cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ⁻¹))).inv.baseHom) ≫ cd.q.baseHom := by
            rw [Category.assoc]
        _ = 𝟙 cd.XM.base ≫ cd.q.baseHom := by rw [hAinv]
        _ = cd.q.baseHom := Category.id_comp _
    calc td.σZ.hom γ ≫ (fell.baseHom ≫ cd.q.baseHom)
        = (td.σZ.hom γ ≫ fell.baseHom) ≫ cd.q.baseHom := (Category.assoc _ _ _).symm
      _ = (fell.baseHom ≫ (cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ⁻¹))).hom.baseHom) ≫
            cd.q.baseHom := congrArg (· ≫ cd.q.baseHom) hbase
      _ = fell.baseHom ≫ ((cd.rM.autMulHom ((P.simulAutSnd Q) (φ γ⁻¹))).hom.baseHom ≫
            cd.q.baseHom) := Category.assoc _ _ _
      _ = fell.baseHom ≫ cd.q.baseHom := congrArg (fell.baseHom ≫ ·) hq'
  -- descend `fell.baseHom ≫ q.base` through the δ-torsor `td.f`
  obtain ⟨f₀, hf₀, -⟩ :=
    existsUnique_descent_of_torsor td.σZ td.over_base td.torsor
      (fell.baseHom ≫ cd.q.baseHom) hinv
  -- the pulled-back torsor projection `sndv` is an epimorphism (finite-étale base change)
  haveI : Flat sndv := by rw [hsndv]; exact MorphismProperty.pullback_snd _ _ ‹Flat cd.q.baseHom›
  haveI : Surjective sndv := by
    rw [hsndv]; exact MorphismProperty.pullback_snd _ _ ‹Surjective cd.q.baseHom›
  haveI : Epi sndv := AlgebraicGeometry.Flat.epi_of_flat_of_surjective sndv
  -- `v.baseHom = f₀`
  have hvf₀ : v.baseHom = f₀ := by
    refine (cancel_epi sndv).mp ?_
    calc sndv ≫ v.baseHom
        = fstv ≫ cd.q.baseHom := hcond.symm
      _ = (θv ≫ fell.baseHom) ≫ cd.q.baseHom := by rw [hI]
      _ = θv ≫ (fell.baseHom ≫ cd.q.baseHom) := by rw [Category.assoc]
      _ = θv ≫ (td.f ≫ f₀) := by rw [← hf₀]
      _ = (θv ≫ td.f) ≫ f₀ := by rw [Category.assoc]
      _ = sndv ≫ f₀ := by rw [hθf]
  rw [hbij, hvf₀]
  exact hf₀

theorem coreData_baseHom_eq (P Q : ModuliProblem R) {G : Type u} [Group G] [Finite G]
    (φ : G →* Aut Q) (htors : ∀ X : EllObj R, Nonempty (TorsorData φ X)) (hrig : P.Rigid)
    (hPrr : P.RelativelyRepresentable) (cd : CoreData P Q φ) (Y : EllObj R)
    (v v' : Y ⟶ cd.X₀) (h : P.map v.op cd.α₀ = P.map v'.op cd.α₀) :
    v.baseHom = v'.baseHom := by
  classical
  obtain ⟨td⟩ := htors Y
  haveI := td.surjective; haveI := td.etale; haveI := td.finite
  haveI : Flat td.f := inferInstance
  haveI : QuasiCompact td.f := inferInstance
  haveI : Epi td.f := AlgebraicGeometry.Flat.epi_of_flat_of_surjective td.f
  -- [B2 GAP — the ONLY remaining hole] `cd.q.baseHom` is a finite étale `G`-torsor.
  -- KM p. 116 (via De-Ga III.2.6.1) needs `𝕸(𝒫,δ) → 𝕸(𝒫,δ)/G` finite étale surjective; the
  -- concrete engine provides it (`etale_quotientπ` + `quotientπ_surjective`, from the derivable
  -- freeness `simulSchemeAction_free_of_rigid`).  But the abstract `CoreData` exposes only
  -- `hqtors` (the `torsorCompare` iso) — provably NOT enough for `Flat`/`Surjective` of
  -- `cd.q.baseHom` (trivial-group ⇒ `hqtors ⇔ mono`, and mono+epi ⇏ flat/surjective in `Scheme`;
  -- `hqlift` closes only the `G = 1` case).  FIX: mirror `TorsorData`'s `surjective`/`etale`/
  -- `finite` fields on `CoreData` (populate in `exists_coreData`), then delete these two lines.
  haveI := cd.hqsurj
  haveI := cd.hqetale
  haveI : Flat cd.q.baseHom := inferInstance
  refine (cancel_epi td.f).mp ?_
  rw [coreData_key P Q φ cd td v, coreData_key P Q φ cd td v', h]

/-- [B3-bij uniqueness b — KM pp. 115–116] G-torsor-map-is-iso ([B2b]) + π-epi. -/
theorem coreData_injective (P Q : ModuliProblem R) {G : Type u} [Group G] [Finite G]
    (φ : G →* Aut Q) (htors : ∀ X : EllObj R, Nonempty (TorsorData φ X)) (hrig : P.Rigid)
    (hPrr : P.RelativelyRepresentable) (cd : CoreData P Q φ) (Y : EllObj R)
    (v v' : Y ⟶ cd.X₀) (h : P.map v.op cd.α₀ = P.map v'.op cd.α₀) : v = v' := by
  classical
  -- Uniqueness reduces (rigidity) to equality of base maps:
  refine coreData_hom_eq_of_baseHom_eq cd hrig v v' ?_ h
  exact coreData_baseHom_eq P Q φ htors hrig hPrr cd Y v v' h

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
