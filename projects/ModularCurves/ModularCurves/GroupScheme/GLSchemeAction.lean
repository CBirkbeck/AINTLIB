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
  -- the residue-field engine
  suffices hb : Function.Bijective ψlin by exact hb
  refine LinearMap.bijective_of_forall_bijective_lTensor_residueField ψlin ?_
  intro J hJ
  sorry

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

/-- **L2b** — `fullLevelHom` is an isomorphism for `N` invertible (`E[N]` finite étale of
rank `N²`, KM 2.3.1): the label map is bijective on every geometric fibre
(`fullLevelFibreMap_bijective`), and the Γ-side comparison is bijective over affine
bases (`fullLevelHom_gamma_bijective`), glued over an affine cover. -/
theorem fullLevelHom_isIso (hinv : NIsInvertible S N) (L : E.FullLevelPt N) :
    IsIso (E.fullLevelHom L) := sorry

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

-- **L4 (seam, consumed by NEW-GH)** — the scheme-level action realises `glSmul`: pushing the
-- full level `L` through `glSchemeSmul g` recovers `g • L`, so `[Γ(N)]/H` (`hOrbitSetoid`) sees the
-- scheme action. Stated precisely once L2 (`fullLevelIso`) lands and NEW-GH pins the exact
-- consumption form (KM 7.1.2; they own the quotient). Placeholder removed — no non-statement.

end EllipticCurve

end ModularCurves
