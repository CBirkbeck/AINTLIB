import ModularCurves.Moduli.GammaH
import ModularCurves.GroupScheme.MuN
import ModularCurves.GroupScheme.TorsionEtaleTriv
import ModularCurves.ForMathlib.FiniteSplitHomDuality
import ModularCurves.ForMathlib.BijectiveResidueField

/-!
# The scheme-level `GL₂(ℤ/N)` action on `E[N]` (CHARTER-C5B-2, reading (1))

`glSmul` (`Moduli/GammaH.lean`) is the `GL₂(ℤ/N)`-action on the *functor-of-points*
`E.FullLevelPt N`. This file upgrades it to the **scheme level**: for `N` invertible on `S`
(so `E[N]` is finite étale of rank `N²`, KM 2.3.1) a naive full level structure `(P,Q)`
trivialises `E[N]` to the constant group scheme `(ℤ/N)²_S`, and each `g ∈ GL₂(ℤ/N)` then
becomes a genuine automorphism of the scheme `E[N] = E.torsion N`.

* `fullLevelIso` (L2, the crux) — the trivialisation `(ℤ/N)²_S ≅ E[N]`.
* `glSchemeSmul` (L3) — the induced `E[N] ≅ E[N]`, with `_one`/`_mul` transported from
  `glSmul_one`/`glSmul_mul`.
* `glSchemeSmul_hOrbit` (L4) — the seam lemma consumed by NEW-GH (Γ_H = `[Γ(N)]/H`).

BOUNDARY: does NOT build the Weil pairing (p2's `[T-C1-KM28]`); cites only the finite-étale
trivialisation infra it shares.
-/

open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

-- v4.33 bump: the `Scheme` category instance inside `appTop`/`pointToTorsion` arguments is
-- no longer transparent enough for the `≫`-associativity rewrites below.
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S) {N : ℕ} [NeZero N]

/-- **L2a** — the trivialisation *map* `φ : (ℤ/N)²_S → E[N]`, `v ↦ (v 0)·P + (v 1)·Q`, built on
`constScheme S A = ∐_A S` by `Sigma.desc` of the torsion sections (`pointToTorsion` of the
`N`-killed combination). -/
noncomputable def fullLevelHom (L : E.FullLevelPt N) :
    constScheme S (Fin 2 → ZMod N) ⟶ E.torsion N :=
  Sigma.desc fun v =>
    E.pointToTorsion (((v 0).val : ℤ) • L.1.1 + ((v 1).val : ℤ) • L.1.2)
      ((E.smul_eq_zero_iff_comp_mulByHom _ N _).mp (by
        rw [smul_add, smul_comm (N : ℤ) ((v 0).val : ℤ), smul_comm (N : ℤ) ((v 1).val : ℤ),
          L.2.1.1, L.2.1.2, smul_zero, smul_zero, add_zero]))

/-- **The affine sections dictionary** (instance-free form): sections of an affine
`X` over a `Spec`-point correspond to ring maps of the section algebras under the
structure triangle. -/
noncomputable def sectionsEquivRingHomUnder {R K : CommRingCat.{u}} {X : Scheme.{u}}
    [IsAffine X] (f : X ⟶ Spec R) (φ : R ⟶ Γ(X, ⊤))
    (hφ : Spec.map φ = X.isoSpec.inv ≫ f) (t : Spec K ⟶ Spec R) :
    { h : Spec K ⟶ X // h ≫ f = t } ≃
      { χ : Γ(X, ⊤) ⟶ K // φ ≫ χ = Spec.preimage t } where
  toFun h := ⟨Spec.preimage (h.1 ≫ X.isoSpec.hom), by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, hφ, Category.assoc,
      Iso.hom_inv_id_assoc]
    exact h.2⟩
  invFun χ := ⟨Spec.map χ.1 ≫ X.isoSpec.inv, by
    rw [Category.assoc, ← hφ, ← Spec.map_comp, χ.2, Spec.map_preimage]⟩
  left_inv h := Subtype.ext (show Spec.map (Spec.preimage (h.1 ≫ X.isoSpec.hom)) ≫
      X.isoSpec.inv = h.1 by
    rw [Spec.map_preimage, Category.assoc, Iso.hom_inv_id, Category.comp_id])
  right_inv χ := Subtype.ext (show Spec.preimage ((Spec.map χ.1 ≫ X.isoSpec.inv) ≫
      X.isoSpec.hom) = χ.1 by
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Spec.preimage_map])

/-- The trivialisation map is a morphism over `S`. -/
@[reassoc]
theorem fullLevelHom_torsionπ (L : E.FullLevelPt N) :
    E.fullLevelHom L ≫ E.torsionπ N = constSchemeπ S (Fin 2 → ZMod N) := by
  refine Sigma.hom_ext _ _ fun v => ?_
  rw [← Category.assoc, fullLevelHom, Sigma.ι_desc, constSchemeπ, Sigma.ι_desc]
  exact E.pointToTorsion_torsionπ _ _

/-- The geometric-fibre label map of a full level structure:
`v ↦ v₀·P + v₁·Q` into the `N`-torsion of the fibre. -/
noncomputable def fullLevelFibreMap (L : E.FullLevelPt N) {k : Type u} [Field k]
    (t : Spec (CommRingCat.of k) ⟶ S) (v : Fin 2 → ZMod N) :
    Submodule.torsionBy ℤ (E.Point t) (N : ℤ) :=
  ⟨((v 0).val : ℤ) • Point.pull E t L.1.1 + ((v 1).val : ℤ) • Point.pull E t L.1.2, by
    have hP : (N : ℤ) • Point.pull E t L.1.1 = 0 := by
      rw [← Point.pull_zsmul, L.2.1.1, Point.pull_zero]
    have hQ : (N : ℤ) • Point.pull E t L.1.2 = 0 := by
      rw [← Point.pull_zsmul, L.2.1.2, Point.pull_zero]
    rw [Submodule.mem_torsionBy_iff, smul_add, smul_comm ((N : ℤ)) (((v 0).val : ℤ)),
      smul_comm ((N : ℤ)) (((v 1).val : ℤ)), hP, hQ, smul_zero, smul_zero, add_zero]⟩

/-- **`L2b-i` — fibrewise bijectivity of a full level structure**: on every geometric
fibre with `N` invertible the label map is a bijection onto the `N`-torsion — surjective
by the generation clause of `IsNaiveFullLevel`, bijective by the `N²`-count
(`torsion_geometricFibre_rank_two`). -/
theorem fullLevelFibreMap_bijective (L : E.FullLevelPt N) {k : Type u} [Field k]
    [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S) (hN : (N : k) ≠ 0) :
    Function.Bijective (E.fullLevelFibreMap L t) := by
  refine (Nat.bijective_iff_surjective_and_card _).mpr ⟨?_, ?_⟩
  · rintro ⟨x, hx⟩
    have hgen := L.2.2 k t x ((Submodule.mem_torsionBy_iff _ _).mp hx)
    rw [AddSubgroup.mem_closure_pair] at hgen
    obtain ⟨a, b, hab⟩ := hgen
    have hP : (N : ℤ) • Point.pull E t L.1.1 = 0 := by
      rw [← Point.pull_zsmul, L.2.1.1, Point.pull_zero]
    have hQ : (N : ℤ) • Point.pull E t L.1.2 = 0 := by
      rw [← Point.pull_zsmul, L.2.1.2, Point.pull_zero]
    refine ⟨![(a : ZMod N), (b : ZMod N)], ?_⟩
    apply Subtype.ext
    show (((![(a : ZMod N), (b : ZMod N)] 0).val : ℤ)) • Point.pull E t L.1.1 +
        (((![(a : ZMod N), (b : ZMod N)] 1).val : ℤ)) • Point.pull E t L.1.2 = x
    have h1 : ((((a : ZMod N)).val : ℤ)) • Point.pull E t L.1.1
        = a • Point.pull E t L.1.1 :=
      zsmul_eq_of_intCast_eq _ hP (by push_cast [ZMod.natCast_val, ZMod.intCast_cast]; simp)
    have h2 : ((((b : ZMod N)).val : ℤ)) • Point.pull E t L.1.2
        = b • Point.pull E t L.1.2 :=
      zsmul_eq_of_intCast_eq _ hQ (by push_cast [ZMod.natCast_val, ZMod.intCast_cast]; simp)
    rw [show ![(a : ZMod N), (b : ZMod N)] 0 = (a : ZMod N) from rfl,
      show ![(a : ZMod N), (b : ZMod N)] 1 = (b : ZMod N) from rfl, h1, h2, hab]
  · have hcard := E.torsion_geometricFibre_rank_two N k t hN
    obtain ⟨e⟩ := hcard
    exact (Nat.card_congr e.toEquiv).symm

/-- **L2b, Γ-side residual (sharp)**: the global-sections comparison of the
trivialisation map over an affine base is bijective. Route: the residue-field engine
(`LinearMap.bijective_of_forall_bijective_lTensor_residueField`) + field-extension
descent + the split hom-duality criterion (`bijective_of_precomp_bijective`) against
the PROVEN fibrewise bijectivity (`fullLevelFibreMap_bijective`), through the Γ–Spec
point dictionary at geometric fibres. -/
theorem fullLevelHom_gamma_bijective {R : CommRingCat.{u}}
    (E : EllipticCurve (Spec R)) {N : ℕ} [NeZero N]
    (hinv : NIsInvertible (Spec R) N) (L : E.FullLevelPt N) :
    Function.Bijective (Spec.preimage
      ((constSchemeSpecIso R (Fin 2 → ZMod N)).inv ≫ E.fullLevelHom L ≫
        (haveI : IsFinite (E.torsionπ N) := E.torsionπ_isFinite N
         haveI : IsAffine (E.torsion N) := isAffine_of_isAffineHom (E.torsionπ N)
         (E.torsion N).isoSpec.hom))).hom := by
  haveI : IsFinite (E.torsionπ N) := E.torsionπ_isFinite N
  haveI : IsAffine (E.torsion N) := isAffine_of_isAffineHom (E.torsionπ N)
  set g : Spec (CommRingCat.of ((Fin 2 → ZMod N) → (R : Type u))) ⟶
      Spec Γ(E.torsion N, ⊤) :=
    (constSchemeSpecIso R (Fin 2 → ZMod N)).inv ≫ E.fullLevelHom L ≫
      (E.torsion N).isoSpec.hom with hg
  set ψ : Γ(E.torsion N, ⊤) ⟶ CommRingCat.of ((Fin 2 → ZMod N) → (R : Type u)) :=
    Spec.preimage g with hψdef
  have hψ : Spec.map ψ = g := Spec.map_preimage g
  -- the structure map of the torsion sections
  set φt : R ⟶ Γ(E.torsion N, ⊤) :=
    Spec.preimage ((E.torsion N).isoSpec.inv ≫ E.torsionπ N) with hφt
  have hφtmap : Spec.map φt = (E.torsion N).isoSpec.inv ≫ E.torsionπ N :=
    Spec.map_preimage _
  letI : Algebra (R : Type u) ↑Γ(E.torsion N, ⊤) := φt.hom.toAlgebra
  -- over-`S` compatibility: `ψ` is the ring-level over-`R` map
  have hAlgCompat : φt ≫ ψ = CommRingCat.ofHom (Pi.constRingHom (Fin 2 → ZMod N)
      (R : Type u)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, hg]
    calc ((constSchemeSpecIso R (Fin 2 → ZMod N)).inv ≫ E.fullLevelHom L ≫
          (E.torsion N).isoSpec.hom) ≫ Spec.map φt
        = (constSchemeSpecIso R (Fin 2 → ZMod N)).inv ≫ E.fullLevelHom L ≫
          (E.torsion N).isoSpec.hom ≫ (E.torsion N).isoSpec.inv ≫ E.torsionπ N := by
          rw [hφtmap]
          simp only [Category.assoc]
      _ = (constSchemeSpecIso R (Fin 2 → ZMod N)).inv ≫ E.fullLevelHom L ≫
          E.torsionπ N := by
          rw [Iso.hom_inv_id_assoc]
      _ = (constSchemeSpecIso R (Fin 2 → ZMod N)).inv ≫
          constSchemeπ (Spec R) (Fin 2 → ZMod N) := by
          rw [E.fullLevelHom_torsionπ L]
      _ = Spec.map (CommRingCat.ofHom (Pi.constRingHom (Fin 2 → ZMod N)
            (R : Type u))) := by
          rw [← constSchemeSpecIso_hom_π R (Fin 2 → ZMod N), Iso.inv_hom_id_assoc]
  -- the `R`-linear form of `ψ`
  set ψlin : ↑Γ(E.torsion N, ⊤) →ₗ[(R : Type u)]
      ((Fin 2 → ZMod N) → (R : Type u)) :=
    { toFun := ψ.hom
      map_add' := fun x y => map_add ψ.hom x y
      map_smul' := fun r x => by
        have hcomp := congrArg (fun m : R ⟶ CommRingCat.of ((Fin 2 → ZMod N) →
          (R : Type u)) => m.hom r) hAlgCompat
        simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hcomp
        show ψ.hom (algebraMap (R : Type u) ↑Γ(E.torsion N, ⊤) r * x)
          = r • ψ.hom x
        rw [map_mul]
        show ψ.hom (φt.hom r) * ψ.hom x = r • ψ.hom x
        rw [hcomp]
        ext v
        show Pi.constRingHom (Fin 2 → ZMod N) (R : Type u) r v * ψ.hom x v
          = r * ψ.hom x v
        rfl } with hψlin
  -- finiteness of the section algebra
  haveI hFt : IsFinite (Spec.map φt) := by
    rw [hφtmap]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite)
      (E.torsion N).isoSpec.inv (E.torsionπ N)).mpr inferInstance
  haveI : Module.Finite (R : Type u) ↑Γ(E.torsion N, ⊤) :=
    (IsFinite.SpecMap_iff φt).mp hFt
  haveI hetale : Etale (E.torsionπ N) := E.torsionπ_etale N hinv
  haveI hEφt : Etale (Spec.map φt) := by
    rw [hφtmap]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @Etale)
      (E.torsion N).isoSpec.inv (E.torsionπ N)).mpr hetale
  haveI : Algebra.Etale (R : Type u) ↑Γ(E.torsion N, ⊤) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp hEφt
  -- the residue-field engine
  suffices hb : Function.Bijective ψlin by exact hb
  refine LinearMap.bijective_of_forall_bijective_lTensor_residueField ψlin ?_
  intro J hJ
  refine LinearMap.bijective_lTensor_of_bijective_baseChange_ext ψlin J.ResidueField
    (AlgebraicClosure J.ResidueField) ?_
  -- the k̄-algebra form of the base-changed comparison
  set ψalg : ↑Γ(E.torsion N, ⊤) →ₐ[(R : Type u)] ((Fin 2 → ZMod N) → (R : Type u)) :=
    { toRingHom := ψ.hom
      commutes' := fun r => by
        have h := congrArg (fun m : R ⟶ CommRingCat.of ((Fin 2 → ZMod N) →
          (R : Type u)) => m.hom r) hAlgCompat
        simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
        exact h } with hψalg
  set Ψ : (AlgebraicClosure J.ResidueField) ⊗[↑R] (↑Γ(E.torsion N, ⊤) : Type u)
      →ₐ[AlgebraicClosure J.ResidueField]
      (AlgebraicClosure J.ResidueField) ⊗[↑R] ((Fin 2 → ZMod N) → (R : Type u)) :=
    Algebra.TensorProduct.map (AlgHom.id (AlgebraicClosure J.ResidueField)
      (AlgebraicClosure J.ResidueField)) ψalg with hΨ
  have hfun : ⇑(ψlin.baseChange (AlgebraicClosure J.ResidueField)) = ⇑Ψ := rfl
  rw [hfun]
  -- split instances
  haveI hsplitPi : Algebra.IsFiniteSplit (AlgebraicClosure J.ResidueField)
      ((AlgebraicClosure J.ResidueField) ⊗[(R : Type u)]
        ((Fin 2 → ZMod N) → (R : Type u))) := by
    classical
    refine Algebra.IsFiniteSplit.of_algEquiv
      (S := (Fin 2 → ZMod N) → (AlgebraicClosure J.ResidueField)) ?_
    exact ((Algebra.TensorProduct.piRight (R : Type u)
      (AlgebraicClosure J.ResidueField) (AlgebraicClosure J.ResidueField)
      (fun _ : Fin 2 → ZMod N => (R : Type u))).trans
      (AlgEquiv.piCongrRight fun _ =>
        Algebra.TensorProduct.rid (R : Type u) (AlgebraicClosure J.ResidueField)
          (AlgebraicClosure J.ResidueField))).symm
  haveI hEtBC : Algebra.Etale (AlgebraicClosure J.ResidueField)
      ((AlgebraicClosure J.ResidueField) ⊗[(R : Type u)] ↑Γ(E.torsion N, ⊤)) :=
    inferInstance
  haveI hsplitT : Algebra.IsFiniteSplit (AlgebraicClosure J.ResidueField)
      ((AlgebraicClosure J.ResidueField) ⊗[(R : Type u)] ↑Γ(E.torsion N, ⊤)) :=
    inferInstance
  refine Algebra.IsFiniteSplit.bijective_of_precomp_bijective Ψ ?_
  -- the dual point-map is the fibrewise label map, through the sections dictionary
  set t : Spec (CommRingCat.of (AlgebraicClosure J.ResidueField)) ⟶ Spec R :=
    Spec.map (CommRingCat.ofHom (algebraMap (R : Type u)
      (AlgebraicClosure J.ResidueField))) with ht
  have htpre : Spec.preimage t = CommRingCat.ofHom (algebraMap (R : Type u)
      (AlgebraicClosure J.ResidueField)) := Spec.preimage_map _
  set secE := sectionsEquivRingHomUnder (E.torsionπ N) φt hφtmap t with hsecE
  set ptE := E.torsionPointsEquiv N t with hptE
  have hN : ((N : ℕ) : AlgebraicClosure J.ResidueField) ≠ 0 := by
    have h2 := hinv.map (Scheme.ΓSpecIso R).hom.hom
    rw [map_natCast] at h2
    have h3 := h2.map (algebraMap (R : Type u) (AlgebraicClosure J.ResidueField))
    rw [map_natCast] at h3
    exact h3.ne_zero
  have hfib := E.fullLevelFibreMap_bijective L t hN
  -- the label points of the constant side
  set χlab : (Fin 2 → ZMod N) → (((Fin 2 → ZMod N) → (R : Type u)) →ₐ[(R : Type u)]
      (AlgebraicClosure J.ResidueField)) := fun v =>
    ((Algebra.ofId (R : Type u) (AlgebraicClosure J.ResidueField)).comp
      (Pi.evalAlgHom (R : Type u) (fun _ => (R : Type u)) v)) with hχlab
  -- sections attached to restricted algebra maps
  have hsecArg : ∀ (χ : ↑Γ(E.torsion N, ⊤) →ₐ[(R : Type u)]
      (AlgebraicClosure J.ResidueField)),
      φt ≫ CommRingCat.ofHom χ.toRingHom = Spec.preimage t := by
    intro χ
    apply CommRingCat.hom_ext
    ext r
    show χ (φt.hom r) = (Spec.preimage t).hom r
    rw [htpre]
    exact χ.commutes r
  set sectionOf : (↑Γ(E.torsion N, ⊤) →ₐ[(R : Type u)]
      (AlgebraicClosure J.ResidueField)) →
      { h : Spec (CommRingCat.of (AlgebraicClosure J.ResidueField)) ⟶ E.torsion N //
        h ≫ E.torsionπ N = t } := fun χ =>
    secE.symm ⟨CommRingCat.ofHom χ.toRingHom, hsecArg χ⟩ with hsectionOf
  have hsectionOf_inj : Function.Injective sectionOf := by
    intro χ₁ χ₂ h12
    have h3 := secE.symm.injective h12
    exact AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom
      (congrArg Subtype.val h3))
  -- the restriction of a Pi-side point through Ψ
  have hrestr : ∀ gp : (AlgebraicClosure J.ResidueField) ⊗[↑R]
      ((Fin 2 → ZMod N) → (R : Type u)) →ₐ[AlgebraicClosure J.ResidueField]
        (AlgebraicClosure J.ResidueField),
      (AlgHom.liftEquiv ..).symm (gp.comp Ψ)
        = ((AlgHom.liftEquiv ..).symm gp).comp ψalg := by
    intro gp
    refine AlgHom.ext fun x => ?_
    show (gp.comp Ψ) (1 ⊗ₜ[↑R] x) = gp (1 ⊗ₜ[↑R] (ψalg x))
    rw [AlgHom.comp_apply, hΨ]
    exact congrArg gp (by simp [Algebra.TensorProduct.map_tmul])
  -- the per-label section identity: the geometric heart
  have hkey : ∀ v : Fin 2 → ZMod N,
      Spec.map (CommRingCat.ofHom ((χlab v).comp ψalg).toRingHom) ≫
        (E.torsion N).isoSpec.inv
      = t ≫ Sigma.ι (fun _ : Fin 2 → ZMod N => Spec (R : CommRingCat.{u})) v ≫
          E.fullLevelHom L := by
    intro v
    have hsplit : CommRingCat.ofHom ((χlab v).comp ψalg).toRingHom
        = ψ ≫ CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin 2 → ZMod N =>
            (R : Type u)) v) ≫ CommRingCat.ofHom (algebraMap (R : Type u)
            (AlgebraicClosure J.ResidueField)) := rfl
    rw [hsplit, Spec.map_comp, Spec.map_comp, hψ, hg]
    rw [show Spec.map (CommRingCat.ofHom (Pi.evalRingHom
        (fun _ : Fin 2 → ZMod N => (R : Type u)) v))
      = Sigma.ι (fun _ : Fin 2 → ZMod N => Spec (R : CommRingCat.{u})) v ≫
        (constSchemeSpecIso R (Fin 2 → ZMod N)).hom
      from (constSchemeSpecIso_ι_hom R (Fin 2 → ZMod N) v).symm]
    rw [← ht]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  -- the point of a pulled-back label is the fibre label point
  have hpoint : ∀ v : Fin 2 → ZMod N,
      ptE (sectionOf ((χlab v).comp ψalg)) = E.fullLevelFibreMap L t v := by
    intro v
    apply Subtype.ext
    apply Subtype.ext
    show (sectionOf ((χlab v).comp ψalg)).1 ≫ E.torsionι N
      = ((E.fullLevelFibreMap L t v) : E.Point t).1
    have hval : (sectionOf ((χlab v).comp ψalg)).1
        = Spec.map (CommRingCat.ofHom ((χlab v).comp ψalg).toRingHom) ≫
          (E.torsion N).isoSpec.inv := rfl
    rw [hval, hkey v]
    have hcomp : Sigma.ι (fun _ : Fin 2 → ZMod N => Spec (R : CommRingCat.{u})) v ≫
        E.fullLevelHom L ≫ E.torsionι N
        = (((v 0).val : ℤ) • L.1.1 + ((v 1).val : ℤ) • L.1.2).1 := by
      rw [fullLevelHom, Sigma.ι_desc_assoc, E.pointToTorsion_torsionι]
    simp only [Category.assoc]
    rw [hcomp]
    show t ≫ (((v 0).val : ℤ) • L.1.1 + ((v 1).val : ℤ) • L.1.2).1
      = ((((v 0).val : ℤ) • Point.pull E t L.1.1) +
        (((v 1).val : ℤ) • Point.pull E t L.1.2)).1
    rw [← Point.pull_zsmul, ← Point.pull_zsmul, ← Point.pull_add]
    rfl
  constructor
  · -- injectivity of the dual map
    intro gp₁ gp₂ hgp
    obtain ⟨v₁, hv₁⟩ :=
      AlgHom.eq_comp_evalAlgHom_of_pi ((AlgHom.liftEquiv ..).symm gp₁)
    obtain ⟨v₂, hv₂⟩ :=
      AlgHom.eq_comp_evalAlgHom_of_pi ((AlgHom.liftEquiv ..).symm gp₂)
    have hχ₁ : (AlgHom.liftEquiv ..).symm gp₁ = χlab v₁ := AlgHom.ext fun x => hv₁ x
    have hχ₂ : (AlgHom.liftEquiv ..).symm gp₂ = χlab v₂ := AlgHom.ext fun x => hv₂ x
    have hres : ((χlab v₁).comp ψalg) = ((χlab v₂).comp ψalg) := by
      rw [← hχ₁, ← hχ₂, ← hrestr gp₁, ← hrestr gp₂]
      exact congrArg (AlgHom.liftEquiv ..).symm hgp
    have hveq : v₁ = v₂ := by
      apply hfib.1
      rw [← hpoint v₁, ← hpoint v₂, hres]
    apply (AlgHom.liftEquiv ..).symm.injective
    rw [hχ₁, hχ₂, hveq]
  · -- surjectivity of the dual map
    intro q
    obtain ⟨v, hv⟩ := hfib.2 (ptE (sectionOf ((AlgHom.liftEquiv ..).symm q)))
    refine ⟨(AlgHom.liftEquiv ..) (χlab v), ?_⟩
    apply (AlgHom.liftEquiv ..).symm.injective
    rw [hrestr, Equiv.symm_apply_apply]
    apply hsectionOf_inj
    apply ptE.injective
    rw [hpoint v, hv]

/-- **L2b over an affine base**: the conjugated `Spec`-morphism is an isomorphism, from
the Γ-bijectivity. -/
theorem fullLevelHom_isIso_of_affine {R : CommRingCat.{u}}
    (E : EllipticCurve (Spec R)) {N : ℕ} [NeZero N]
    (hinv : NIsInvertible (Spec R) N) (L : E.FullLevelPt N) :
    IsIso (E.fullLevelHom L) := by
  haveI : IsFinite (E.torsionπ N) := E.torsionπ_isFinite N
  haveI : IsAffine (E.torsion N) := isAffine_of_isAffineHom (E.torsionπ N)
  set g : Spec (CommRingCat.of ((Fin 2 → ZMod N) → (R : Type u))) ⟶
      Spec Γ(E.torsion N, ⊤) :=
    (constSchemeSpecIso R (Fin 2 → ZMod N)).inv ≫ E.fullLevelHom L ≫
      (E.torsion N).isoSpec.hom with hg
  have hbij := E.fullLevelHom_gamma_bijective hinv L
  haveI hisoψ : IsIso (Spec.preimage g) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  haveI hisog : IsIso g := by
    rw [← Spec.map_preimage g]
    infer_instance
  have hfac : E.fullLevelHom L
      = (constSchemeSpecIso R (Fin 2 → ZMod N)).hom ≫ g ≫
        (E.torsion N).isoSpec.inv := by
    rw [hg]
    simp only [Iso.hom_inv_id_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hfac]
  infer_instance

section BaseChangeNaturality

/-- **Base-change naturality of the trivialisation map**: pulling the level structure
back along `σ : T' ⟶ S` intertwines the two `fullLevelHom`s through the constant-scheme
and torsion base-change comparisons. Componentwise: the `v`-combination of the
pulled-back generators is the pullback of the `v`-combination, transported by the
additive dictionary `Point.baseChangeEquiv`. -/
theorem fullLevelHom_baseChange {T' : Scheme.{u}} (σ : T' ⟶ S) (L : E.FullLevelPt N) :
    constSchemeMapAlong σ (Fin 2 → ZMod N) ≫ E.fullLevelHom L
      = (E.baseChange σ).fullLevelHom (L.pullAlong σ) ≫ E.torsionBaseChangeHom N σ := by
  apply Sigma.hom_ext
  intro v
  rw [ι_constSchemeMapAlong_assoc, fullLevelHom, fullLevelHom, Sigma.ι_desc_assoc,
    Sigma.ι_desc]
  apply pullback.hom_ext
  · -- the `torsionι` leg
    show (σ ≫ E.pointToTorsion _ _) ≫ E.torsionι N
      = ((E.baseChange σ).pointToTorsion _ _ ≫ E.torsionBaseChangeHom N σ) ≫ E.torsionι N
    rw [Category.assoc, E.pointToTorsion_torsionι, Category.assoc,
      torsionBaseChangeHom_torsionι, ← Category.assoc,
      (E.baseChange σ).pointToTorsion_torsionι]
    -- transport the combination through the additive base-change dictionary
    have hP : Point.baseChangeEquiv E σ (𝟙 T') (L.pullAlong σ).1.1
        = Point.pull E (𝟙 T' ≫ σ) L.1.1 := by
      refine Subtype.ext ?_
      show (L.pullAlong σ).1.1.1 ≫ pullback.fst E.π σ = (𝟙 T' ≫ σ) ≫ L.1.1.1
      rw [Category.assoc, Category.id_comp]
      exact Point.asSection_val_fst E σ _
    have hQ : Point.baseChangeEquiv E σ (𝟙 T') (L.pullAlong σ).1.2
        = Point.pull E (𝟙 T' ≫ σ) L.1.2 := by
      refine Subtype.ext ?_
      show (L.pullAlong σ).1.2.1 ≫ pullback.fst E.π σ = (𝟙 T' ≫ σ) ≫ L.1.2.1
      rw [Category.assoc, Category.id_comp]
      exact Point.asSection_val_fst E σ _
    have hcomb : Point.baseChangeEquiv E σ (𝟙 T')
        (((v 0).val : ℤ) • (L.pullAlong σ).1.1 + ((v 1).val : ℤ) • (L.pullAlong σ).1.2)
        = Point.pull E (𝟙 T' ≫ σ)
            (((v 0).val : ℤ) • L.1.1 + ((v 1).val : ℤ) • L.1.2) := by
      rw [map_add, map_zsmul, map_zsmul, hP, hQ, Point.pull_add, Point.pull_zsmul,
        Point.pull_zsmul]
    have hval := congrArg Subtype.val hcomb
    rw [Point.baseChangeEquiv_apply_coe] at hval
    rw [hval]
    show (𝟙 T' ≫ σ) ≫ _ = σ ≫ _
    rw [Category.assoc, Category.id_comp]
  · -- the `torsionπ` leg
    show (σ ≫ E.pointToTorsion _ _) ≫ (pullback.snd (E.mulByHom N) E.zero)
      = ((E.baseChange σ).pointToTorsion _ _ ≫ E.torsionBaseChangeHom N σ) ≫
        (pullback.snd (E.mulByHom N) E.zero)
    show (σ ≫ E.pointToTorsion _ _) ≫ E.torsionπ N
      = ((E.baseChange σ).pointToTorsion _ _ ≫ E.torsionBaseChangeHom N σ) ≫ E.torsionπ N
    rw [Category.assoc, E.pointToTorsion_torsionπ, Category.assoc,
      torsionBaseChangeHom_torsionπ, ← Category.assoc,
      (E.baseChange σ).pointToTorsion_torsionπ, Category.id_comp, Category.comp_id]

end BaseChangeNaturality

/-- **The naturality square of `fullLevelHom` is cartesian**: the constant scheme over a
chart is the pullback of the trivialisation map along the torsion base-change
comparison. Vertical pasting (`IsPullback.of_bot`) of the constant-scheme square over
the torsion square. -/
theorem isPullback_fullLevelHom {T' : Scheme.{u}} (σ : T' ⟶ S) (L : E.FullLevelPt N) :
    IsPullback (constSchemeMapAlong σ (Fin 2 → ZMod N))
      ((E.baseChange σ).fullLevelHom (L.pullAlong σ)) (E.fullLevelHom L)
      (E.torsionBaseChangeHom N σ) := by
  refine IsPullback.of_bot ?_ (E.fullLevelHom_baseChange σ L)
    (E.torsion_baseChange_isPullback N σ)
  have hs := isPullback_constSchemeMapAlong σ (Fin 2 → ZMod N)
  rwa [← fullLevelHom_torsionπ (E := E.baseChange σ) (L := L.pullAlong σ),
    ← fullLevelHom_torsionπ (E := E) (L := L)] at hs

/-- **L2b** — `fullLevelHom` is an isomorphism for `N` invertible (`E[N]` finite étale of
rank `N²`, KM 2.3.1): over each affine chart the comparison is an isomorphism
(`fullLevelHom_isIso_of_affine`), and being an isomorphism is Zariski-local on the
target — the charts of the torsion scheme are the base-change comparisons over an
affine cover of `S`, along which `fullLevelHom` pulls back to the chart-level
trivialisations (`isPullback_fullLevelHom`). -/
theorem fullLevelHom_isIso (hinv : NIsInvertible S N) (L : E.FullLevelPt N) :
    IsIso (E.fullLevelHom L) := by
  let 𝒰₀ := S.affineCover
  -- the base-change comparisons are jointly surjective open immersions
  have hrange : ∀ i : 𝒰₀.I₀, Set.range (E.torsionBaseChangeHom N (𝒰₀.f i))
      = ⇑(E.torsionπ N) ⁻¹' Set.range (𝒰₀.f i) := by
    intro i
    have h := E.torsion_baseChange_isPullback N (𝒰₀.f i)
    rw [← h.isoPullback_hom_fst]
    calc Set.range ⇑(h.isoPullback.hom ≫ pullback.fst (E.torsionπ N) (𝒰₀.f i))
        = Set.range (⇑(pullback.fst (E.torsionπ N) (𝒰₀.f i)) ∘ ⇑h.isoPullback.hom) := rfl
      _ = ⇑(pullback.fst (E.torsionπ N) (𝒰₀.f i)) '' Set.range ⇑h.isoPullback.hom :=
          Set.range_comp _ _
      _ = ⇑(pullback.fst (E.torsionπ N) (𝒰₀.f i)) '' Set.univ := by
          haveI : Surjective h.isoPullback.hom := inferInstance
          rw [h.isoPullback.hom.surjective.range_eq]
      _ = Set.range ⇑(pullback.fst (E.torsionπ N) (𝒰₀.f i)) := Set.image_univ
      _ = ⇑(E.torsionπ N) ⁻¹' Set.range (𝒰₀.f i) := Scheme.Pullback.range_fst _ _
  haveI hOI : ∀ i : 𝒰₀.I₀, IsOpenImmersion (E.torsionBaseChangeHom N (𝒰₀.f i)) := by
    intro i
    have h := E.torsion_baseChange_isPullback N (𝒰₀.f i)
    rw [← h.isoPullback_hom_fst]
    infer_instance
  let 𝒰 : (E.torsion N).OpenCover := Scheme.Cover.mkOfCovers 𝒰₀.I₀
    (fun i => (E.baseChange (𝒰₀.f i)).torsion N)
    (fun i => E.torsionBaseChangeHom N (𝒰₀.f i))
    (fun x => by
      obtain ⟨i, y₀, hy₀⟩ := 𝒰₀.exists_eq ((E.torsionπ N) x)
      have hx : x ∈ Set.range (E.torsionBaseChangeHom N (𝒰₀.f i)) := by
        rw [hrange i]
        exact ⟨y₀, hy₀⟩
      obtain ⟨y, hy⟩ := hx
      exact ⟨i, y, hy⟩)
  have hloc : (MorphismProperty.isomorphisms Scheme.{u}) (E.fullLevelHom L) := by
    refine (IsZariskiLocalAtTarget.iff_of_openCover
      (P := MorphismProperty.isomorphisms Scheme.{u}) (f := E.fullLevelHom L) 𝒰).mpr
      fun i => ?_
    show IsIso (pullback.snd (E.fullLevelHom L) (E.torsionBaseChangeHom N (𝒰₀.f i)))
    have hA := E.isPullback_fullLevelHom (𝒰₀.f i) L
    haveI : IsIso ((E.baseChange (𝒰₀.f i)).fullLevelHom (L.pullAlong (𝒰₀.f i))) :=
      fullLevelHom_isIso_of_affine (E.baseChange (𝒰₀.f i))
        (NIsInvertible.of_hom (𝒰₀.f i) hinv) (L.pullAlong (𝒰₀.f i))
    rw [show pullback.snd (E.fullLevelHom L) (E.torsionBaseChangeHom N (𝒰₀.f i))
        = hA.isoPullback.inv ≫ (E.baseChange (𝒰₀.f i)).fullLevelHom (L.pullAlong (𝒰₀.f i))
      from by rw [Iso.eq_inv_comp]; exact hA.isoPullback_hom_snd]
    infer_instance
  exact hloc

/-- **L2 (crux)** — a naive full level-`N` structure trivialises `E[N]` to the constant scheme
`(ℤ/N)²_S`, for `N` invertible on `S`. -/
noncomputable def fullLevelIso (hinv : NIsInvertible S N) (L : E.FullLevelPt N) :
    constScheme S (Fin 2 → ZMod N) ≅ E.torsion N :=
  haveI := E.fullLevelHom_isIso hinv L
  asIso (E.fullLevelHom L)

/-- `g ∈ GL₂(ℤ/N)` as a linear bijection of `Fin 2 → ZMod N` (matrix-vector multiplication;
inverse via `g⁻¹`). -/
def glEquiv (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    (Fin 2 → ZMod N) ≃ (Fin 2 → ZMod N) where
  toFun v := (g : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec v
  invFun v := ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec v
  left_inv v := by
    show ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
        Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec
        ((g : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec v) = v
    rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  right_inv v := by
    show ((g : Matrix (Fin 2) (Fin 2) (ZMod N))).mulVec
        (((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
          Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec v) = v
    rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]

@[simp] theorem glEquiv_one : glEquiv (1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) = Equiv.refl _ := by
  ext v; simp [glEquiv, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]

theorem glEquiv_mul (g h : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    glEquiv (g * h) = (glEquiv h).trans (glEquiv g) := by
  ext v
  simp only [glEquiv, Equiv.coe_fn_mk, Equiv.trans_apply, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.mulVec_mulVec]

/-- The constant automorphism of `(ℤ/N)²_S` induced by `g ∈ GL₂(ℤ/N)` acting linearly on
`Fin 2 → ZMod N`. Built directly on `constScheme S A = ∐_A S`. -/
noncomputable def constGL (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    constScheme S (Fin 2 → ZMod N) ≅ constScheme S (Fin 2 → ZMod N) where
  hom := Sigma.desc fun a => Sigma.ι (fun _ : (Fin 2 → ZMod N) => S) (glEquiv g a)
  inv := Sigma.desc fun a => Sigma.ι (fun _ : (Fin 2 → ZMod N) => S) ((glEquiv g).symm a)
  hom_inv_id := by
    refine Sigma.hom_ext _ _ fun a => ?_
    simp only [Sigma.ι_desc_assoc, Sigma.ι_desc, Category.comp_id, Equiv.symm_apply_apply]
  inv_hom_id := by
    refine Sigma.hom_ext _ _ fun a => ?_
    simp only [Sigma.ι_desc_assoc, Sigma.ι_desc, Category.comp_id, Equiv.apply_symm_apply]

@[simp] theorem constGL_one : constGL (S := S) (1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) = Iso.refl _ := by
  ext1
  refine Sigma.hom_ext _ _ fun a => ?_
  simp only [constGL, glEquiv_one, Equiv.refl_apply, Sigma.ι_desc, Iso.refl_hom, Category.comp_id]

theorem constGL_mul (g h : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    constGL (S := S) (g * h) = constGL (S := S) h ≪≫ constGL (S := S) g := by
  ext1
  refine Sigma.hom_ext _ _ fun a => ?_
  simp only [constGL, glEquiv_mul, Equiv.trans_apply, Iso.trans_hom, Sigma.ι_desc_assoc,
    Sigma.ι_desc]

/-- **L3** — the scheme-level `GL₂(ℤ/N)` action on `E[N] = E.torsion N`, obtained by
transporting the constant linear automorphism through the trivialisation `fullLevelIso`. -/
noncomputable def glSchemeSmul (hinv : NIsInvertible S N)
    (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) (L : E.FullLevelPt N) :
    E.torsion N ≅ E.torsion N :=
  (E.fullLevelIso hinv L).symm ≪≫ constGL (S := S) g ≪≫ E.fullLevelIso hinv L

/-- The identity acts trivially (transported from `glSmul_one`). -/
theorem glSchemeSmul_one (hinv : NIsInvertible S N) (L : E.FullLevelPt N) :
    E.glSchemeSmul hinv 1 L = Iso.refl _ := by
  rw [glSchemeSmul, constGL_one, Iso.refl_trans, Iso.symm_self_id]

/-- Multiplicativity of the scheme-level action (transported from `constGL_mul` + the
`fullLevelIso ≪≫ fullLevelIso.symm` cancellation). -/
theorem glSchemeSmul_mul (hinv : NIsInvertible S N)
    (g h : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) (L : E.FullLevelPt N) :
    E.glSchemeSmul hinv (g * h) L
      = E.glSchemeSmul hinv h L ≪≫ E.glSchemeSmul hinv g L := by
  rw [glSchemeSmul, glSchemeSmul, glSchemeSmul, constGL_mul]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]

section Seam

/-- **L4 (seam)** — the constant linear automorphism realises `glSmul` through the
trivialisation map: `constGL g` followed by the `L`-trivialisation is the
`g • L`-trivialisation. Componentwise: bilinearity of the Drinfeld combination in the
`ZMod N` valuations (`val_smul_add`/`val_smul_mul` + `module`). -/
theorem constGL_hom_fullLevelHom (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
    (L : E.FullLevelPt N) :
    (constGL (S := S) g).hom ≫ E.fullLevelHom L = E.fullLevelHom (E.glSmul g L) := by
  refine Sigma.hom_ext _ _ fun v => ?_
  show Sigma.ι (fun _ : (Fin 2 → ZMod N) => S) v ≫ Sigma.desc (fun a =>
      Sigma.ι (fun _ : (Fin 2 → ZMod N) => S) (glEquiv g a)) ≫ E.fullLevelHom L
    = Sigma.ι (fun _ : (Fin 2 → ZMod N) => S) v ≫ E.fullLevelHom (E.glSmul g L)
  rw [Sigma.ι_desc_assoc, fullLevelHom, fullLevelHom, Sigma.ι_desc, Sigma.ι_desc]
  have hP : (N : ℤ) • L.1.1 = 0 := L.2.1.1
  have hQ : (N : ℤ) • L.1.2 = 0 := L.2.1.2
  have harith : ((glEquiv g v 0).val : ℤ) • L.1.1 + ((glEquiv g v 1).val : ℤ) • L.1.2
      = ((v 0).val : ℤ) • (E.glSmul g L).1.1 + ((v 1).val : ℤ) • (E.glSmul g L).1.2 := by
    show ((((g : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec v) 0).val : ℤ) • L.1.1
        + ((((g : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec v) 1).val : ℤ) • L.1.2
      = ((v 0).val : ℤ) • ((((g : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0).val : ℤ) • L.1.1
          + (((g : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0).val : ℤ) • L.1.2)
        + ((v 1).val : ℤ) • ((((g : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 1).val : ℤ) • L.1.1
          + (((g : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 1).val : ℤ) • L.1.2)
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [val_smul_add E L.1.1 hP, val_smul_add E L.1.2 hQ,
      val_smul_mul E L.1.1 hP, val_smul_mul E L.1.1 hP,
      val_smul_mul E L.1.2 hQ, val_smul_mul E L.1.2 hQ]
    module
  simp only [harith]

/-- The trivialisation of `g • L` is `constGL g` followed by the `L`-trivialisation. -/
theorem fullLevelIso_glSmul (hinv : NIsInvertible S N)
    (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) (L : E.FullLevelPt N) :
    E.fullLevelIso hinv (E.glSmul g L) = constGL (S := S) g ≪≫ E.fullLevelIso hinv L := by
  ext1
  show E.fullLevelHom (E.glSmul g L) = (constGL (S := S) g).hom ≫ E.fullLevelHom L
  exact (E.constGL_hom_fullLevelHom g L).symm

/-- **L4 (orbit form, consumed by NEW-GH)** — the transition between the trivialisations
of two `glSmul`-related full level structures IS the scheme-level action of the
connecting matrix. -/
theorem fullLevelIso_symm_trans_of_glSmul_eq (hinv : NIsInvertible S N)
    {g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)} {L L' : E.FullLevelPt N}
    (h : E.glSmul g L = L') :
    (E.fullLevelIso hinv L).symm ≪≫ E.fullLevelIso hinv L' = E.glSchemeSmul hinv g L := by
  subst h
  rw [fullLevelIso_glSmul, glSchemeSmul]

/-- **L4 (hOrbit form)** — `hOrbitSetoid`-equivalent level structures have trivialisations
differing by the scheme action of an element of `H`: the torsion trivialisation is
well defined on `[Γ(N)]/H`-classes modulo `glSchemeSmul H`. -/
theorem exists_glSchemeSmul_of_hOrbit (hinv : NIsInvertible S N)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    {L L' : E.FullLevelPt N} (h : (E.hOrbitSetoid H).r L L') :
    ∃ g ∈ H, (E.fullLevelIso hinv L).symm ≪≫ E.fullLevelIso hinv L'
      = E.glSchemeSmul hinv g L := by
  obtain ⟨g, hg, hgl⟩ := h
  exact ⟨g, hg, E.fullLevelIso_symm_trans_of_glSmul_eq hinv hgl⟩

end Seam

end EllipticCurve

end ModularCurves
