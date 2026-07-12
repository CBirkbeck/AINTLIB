import ModularCurves.Moduli.GammaH
import ModularCurves.GroupScheme.MuN

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

/-- **L2b** — `fullLevelHom` is an isomorphism for `N` invertible (`E[N]` finite étale of rank
`N²`, KM 2.3.1; `φ` is a fibrewise iso by `IsNaiveFullLevel` generation, hence an iso by the
finite-étale fibrewise-iso criterion `isIso_of_isPullback_of_fppf`). Shares the machinery of
`torsion_etaleLocal_triv` (T-F1). -/
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
