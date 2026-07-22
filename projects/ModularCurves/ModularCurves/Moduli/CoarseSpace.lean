/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

STREAM-Y0 skeleton (M3 = Option 2, user-ratified 2026-07-22). Decomposition of record:
`.mathlib-quality/decomposition-coarse-y0.md`.
-/
import ModularCurves.Moduli.GammaHClosure
import ModularCurves.Moduli.GammaHSemiBorel

/-!
# The coarse modular curve `M(𝒫) = 𝔐(𝒫,δ)/G` at `δ = [Γ(N)]` — KM 8.1.1, fixed base

**KM 8.1.1 (print p. 224, verbatim):** "Let R be a ring, 𝒫 a relatively representable
moduli problem on (Ell/R) which is affine over (Ell/R). We will recall the definition
of the 'coarse moduli scheme' M(𝒫). This is an R-scheme which agrees with 𝔐(𝒫) for
representable 𝒫, and which is a 'best replacement' if 𝒫 is not representable. To
define M(𝒫) as an R-scheme, it suffices to do so locally on R. So we may assume that
some integer N ≥ 3 is invertible in R. Let δ be any representable moduli problem which
is finite etale galois over (Ell/R), with galois group G (e.g., δ = [Γ(N)],
G = GL(2, ℤ/Nℤ)). We define M(𝒫) as the quotient scheme M(𝒫) = 𝔐(𝒫, δ)/G. The
resulting R-scheme is clearly independent of the auxiliary choice of δ (and so patches
together). It 'exists' because 𝔐(𝒫, δ) is itself affine."

**Fixed-base specialization of record (Option 2):** over our fixed `R` with
`IsUnit (N : R)` and `N ≥ 3`, the auxiliary `δ := [Γ(N)]` is itself representable
in-tree (`gammaFullNaive_rigid_and_representable`), so no localization on `R` and no
`δ`-independence are needed: for `𝒫 = [Γ(N)]/H` (KM 7.4.2(4): "[Γ₀(N)] … the quotient
of [Γ(N)] by the Borel subgroup (∗ ∗; 0 ∗)"), KM 8.1.5 ("M(𝒫)/G ≅ M(𝒫/G)", p. 226)
collapses the definition to the quotient of the representing scheme itself:
`Y_H := 𝔐([Γ(N)]).base / H`, executed by the diagonal-free relative-invariant-Spec
engine (`ForMathlib/RelativeInvariantSpec.lean`, PROVEN). `Y₀(N)` is the Borel
instance. NO base-change functoriality is claimed (KM Remark 8.1.7: "Formation of the
coarse moduli scheme does not always commute with base change").

The scheme represents nothing (Loeffler 3.8.3: `−1 ∈ Γ₀(N)` kills rigidity — in-tree
no-go `hH_refuted_of_neg_one_mem`); its contract is the categorical-quotient universal
property (Loeffler Prop 3.6.1) delivered by `existsUnique_relQuotientπ_lift`, plus
projection/structure morphism properties. The KM 8.1.3.1 geometric-points description
is a P2 follow-on (needs a KM A7.2.2 source pass).
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace ModularCurves

variable {R : CommRingCat.{u}}

/-! ## The `Aut`-transport to the base scheme -/

namespace ModuliProblem

/-- **The scheme action of a problem-automorphism group on the base of a representing
object** (KM 8.1.1's `G`-action on `𝔐(𝒫,δ)`): transport `φ : G →* Aut P` through the
representation (`RepresentableBy.autMulHom`, Yoneda) and project to the base scheme
(`EllObj.autBase`); `SchemeAction.ofAut` normalizes the variance — the absolute-level
mirror of `simulSchemeAction` (`Moduli/QuotientProblem.lean:606`). -/
noncomputable def _root_.CategoryTheory.Functor.RepresentableBy.baseSchemeAction
    {P : ModuliProblem R} {X₀ : EllObj R} (r : P.RepresentableBy X₀)
    {G : Type*} [Group G] (φ : G →* Aut P) : SchemeAction G X₀.base :=
  AlgebraicGeometry.SchemeAction.ofAut ((X₀.autBase.comp r.autMulHom).comp φ)

/-- The transported action lies over `Spec R` (`EllHom.base_w` of the transported
automorphisms). -/
theorem _root_.CategoryTheory.Functor.RepresentableBy.baseSchemeAction_over
    {P : ModuliProblem R} {X₀ : EllObj R} (r : P.RepresentableBy X₀)
    {G : Type*} [Group G] (φ : G →* Aut P) (γ : G) :
    (r.baseSchemeAction φ).hom γ ≫ X₀.structMap = X₀.structMap :=
  (r.autMulHom (φ γ)).inv.base_w

/-! ## Affineness of the representing base (KM 8.1.1: "𝔐(𝒫,δ) is itself affine") -/

/-- Affineness of the base transports between representing objects
(`RepresentableBy.uniqueUpToIso` + `IsAffine.of_isIso` on the base leg — the
`EngineWiring` `hQaff` idiom, made a standalone lemma). -/
theorem _root_.CategoryTheory.Functor.RepresentableBy.isAffine_base_transport
    {P : ModuliProblem R} {X Y : EllObj R} (rX : P.RepresentableBy X)
    (rY : P.RepresentableBy Y) (h : IsAffine X.base) : IsAffine Y.base := by
  let e : Y ≅ X := rY.uniqueUpToIso rX
  haveI := h
  haveI : IsIso e.hom.baseHom := ⟨e.inv.baseHom,
    congrArg EllHom.baseHom e.hom_inv_id, congrArg EllHom.baseHom e.inv_hom_id⟩
  exact IsAffine.of_isIso e.hom.baseHom

/-- **[Y0-AFF5] The full-level problem is representable by an object with affine
base** (`N ≥ 3` invertible): the D(2)/D(3) recollement of the two engine outputs, each
of which is `𝔐(𝒫,δ)/G` with `𝔐(𝒫,δ)` affine (KM 8.1.1's existence sentence), glued
along `D(2) ∪ D(3) = Spec R`; the glued structure morphism is affine target-locally. -/
theorem gammaFullNaive_exists_representableBy_isAffineHom (N : ℕ) [NeZero N]
    (hN : 3 ≤ (N : ℤ)) (hinv : IsUnit (N : R)) :
    ∃ X : EllObj R, IsAffineHom X.structMap ∧
      Nonempty ((gammaFullNaiveProblem R N).RepresentableBy X) := by
  exact exists_representableBy_isAffineHom_of_baseChange_cover
    (gammaFullNaiveProblem R N) 2 3 ⟨-1, 1, by ring⟩
    (gammaFullNaive_affineOverEll R N hinv).relativelyRepresentable
    (ModuliProblem.exists_representableBy_isAffine_baseChange_two R
      (gammaFullNaiveProblem R N) (gammaFullNaive_affineOverEll R N hinv)
      (gammaFullNaive_rigidNoeth R N hN hinv))
    (ModuliProblem.exists_representableBy_isAffine_baseChange_three R
      (gammaFullNaiveProblem R N) (gammaFullNaive_affineOverEll R N hinv)
      (gammaFullNaive_rigidNoeth R N hN hinv))

/-- Affineness of the structure morphism for EVERY representing object of the
full-level problem (transport of [Y0-AFF5] along the unique iso). -/
theorem gammaFullNaive_isAffineHom_structMap (N : ℕ) [NeZero N]
    (hN : 3 ≤ (N : ℤ)) (hinv : IsUnit (N : R)) {X : EllObj R}
    (r : (gammaFullNaiveProblem R N).RepresentableBy X) :
    IsAffineHom X.structMap := by
  obtain ⟨X₀, hX₀, ⟨r₀⟩⟩ :=
    gammaFullNaive_exists_representableBy_isAffineHom (R := R) N hN hinv
  let e : X ≅ X₀ := r.uniqueUpToIso r₀
  haveI : IsIso e.hom.baseHom := ⟨e.inv.baseHom,
    congrArg EllHom.baseHom e.hom_inv_id, congrArg EllHom.baseHom e.inv_hom_id⟩
  haveI := hX₀
  rw [← e.hom.base_w]
  infer_instance

/-! ## The coarse quotient (KM 8.1.1, fixed-base form) -/

section CoarseQuotient

variable {P : ModuliProblem R} {X₀ : EllObj R} {G : Type*} [Group G] [Finite G]

/-- **The coarse quotient scheme `M(P/G) = 𝔐(P).base/G`** (KM 8.1.1 at `δ = P`
representable + KM 8.1.5): the relative-invariant-Spec quotient of the representing
base by the transported action. -/
noncomputable def _root_.CategoryTheory.Functor.RepresentableBy.coarseQuotient
    (r : P.RepresentableBy X₀) (φ : G →* Aut P) [IsAffineHom X₀.structMap] :
    Scheme.{u} :=
  (r.baseSchemeAction φ).relQuotient X₀.structMap (r.baseSchemeAction_over φ)

/-- The quotient projection `𝔐(P).base ⟶ M(P/G)`. -/
noncomputable def _root_.CategoryTheory.Functor.RepresentableBy.coarsePr
    (r : P.RepresentableBy X₀) (φ : G →* Aut P) [IsAffineHom X₀.structMap] :
    X₀.base ⟶ r.coarseQuotient φ :=
  (r.baseSchemeAction φ).relQuotientπ X₀.structMap (r.baseSchemeAction_over φ)

/-- The structure morphism `M(P/G) ⟶ Spec R`. -/
noncomputable def _root_.CategoryTheory.Functor.RepresentableBy.coarseStruct
    (r : P.RepresentableBy X₀) (φ : G →* Aut P) [IsAffineHom X₀.structMap] :
    r.coarseQuotient φ ⟶ Spec R :=
  (r.baseSchemeAction φ).relQuotientStruct X₀.structMap (r.baseSchemeAction_over φ)

variable (r : P.RepresentableBy X₀) (φ : G →* Aut P) [IsAffineHom X₀.structMap]

/-- The projection lies over `Spec R`. -/
theorem _root_.CategoryTheory.Functor.RepresentableBy.coarsePr_comp_coarseStruct :
    r.coarsePr φ ≫ r.coarseStruct φ = X₀.structMap :=
  (r.baseSchemeAction φ).relQuotientπ_comp_relQuotientStruct X₀.structMap
    (r.baseSchemeAction_over φ)

/-- The projection coequalizes the action. -/
theorem _root_.CategoryTheory.Functor.RepresentableBy.baseSchemeAction_comp_coarsePr
    (γ : G) : (r.baseSchemeAction φ).hom γ ≫ r.coarsePr φ = r.coarsePr φ :=
  (r.baseSchemeAction φ).hom_comp_relQuotientπ X₀.structMap
    (r.baseSchemeAction_over φ) γ

/-- **The categorical-quotient universal property** (Loeffler Prop 3.6.1: the unique
`S`-scheme "representing the functor `Y ↦ (homs of S-schemes X → Y commuting with the
G-action)`"; KM 8.1.1's quotient): every invariant morphism factors uniquely. -/
theorem _root_.CategoryTheory.Functor.RepresentableBy.coarsePr_existsUnique_lift
    {Y : Scheme.{u}} (F : X₀.base ⟶ Y)
    (hF : ∀ γ : G, (r.baseSchemeAction φ).hom γ ≫ F = F) :
    ∃! q : r.coarseQuotient φ ⟶ Y, r.coarsePr φ ≫ q = F :=
  (r.baseSchemeAction φ).existsUnique_relQuotientπ_lift X₀.structMap
    (r.baseSchemeAction_over φ) F hF

/-- The projection is integral (KM 7.1.3(4) via the engine; no freeness needed). -/
instance : IsIntegralHom (r.coarsePr φ) :=
  (r.baseSchemeAction φ).isIntegralHom_relQuotientπ X₀.structMap
    (r.baseSchemeAction_over φ)

/-- The projection is surjective. -/
instance : Surjective (r.coarsePr φ) :=
  (r.baseSchemeAction φ).surjective_relQuotientπ_of_free X₀.structMap
    (r.baseSchemeAction_over φ)

/-- The structure morphism of the coarse space is affine (chartwise
`Spec Γ(𝔐(P).base, ·)ᴳ`; in particular the coarse space is an affine scheme over the
affine `Spec R`). -/
instance : IsAffineHom (r.coarseStruct φ) :=
  (r.baseSchemeAction φ).isAffineHom_relQuotientStruct X₀.structMap
    (r.baseSchemeAction_over φ)

end CoarseQuotient

end ModuliProblem

/-! ## `Y_H` and `Y₀(N)` -/

/-- The Borel subgroup `{(∗ ∗; 0 ∗)}` of `GL₂(ℤ/N)` (KM 7.4.2(4)). -/
def borel (N : ℕ) [NeZero N] :
    Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0 = 0}
  mul_mem' := by
    rintro a b ha hb
    show ((a : Matrix (Fin 2) (Fin 2) (ZMod N)) * b) 1 0 = 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, ha, hb, zero_mul, mul_zero, add_zero]
  one_mem' := by
    show (1 : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0 = 0
    simp
  inv_mem' := by
    rintro g h10
    have hmul : (g : Matrix (Fin 2) (Fin 2) (ZMod N)) *
        ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
          Matrix (Fin 2) (Fin 2) (ZMod N)) = 1 := g.mul_inv
    have h11 : IsUnit ((g : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 1) := by
      have hdet : IsUnit (g : Matrix (Fin 2) (Fin 2) (ZMod N)).det :=
        (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
      rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
      exact (IsUnit.mul_iff.mp hdet).2
    have e10 : ((g : Matrix (Fin 2) (Fin 2) (ZMod N)) *
        ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
          Matrix (Fin 2) (Fin 2) (ZMod N))) 1 0 = 0 := by
      rw [hmul]; simp
    rw [Matrix.mul_apply, Fin.sum_univ_two, h10, zero_mul, zero_add] at e10
    exact (IsUnit.mul_right_eq_zero h11).mp e10

/-- Membership in the Borel subgroup, unfolded. -/
theorem mem_borel_iff (N : ℕ) [NeZero N]
    (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    g ∈ borel N ↔ (g : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0 = 0 :=
  Iff.rfl

/-- The semi-Borel is contained in the Borel. -/
theorem semiBorel_le_borel (N : ℕ) [NeZero N] : semiBorel N ≤ borel N :=
  fun _ hg => hg.2

/-- **The coarse modular curve `Y_H` over `R`** (`N ≥ 3` invertible): the quotient of
the full-level modular curve `Y(N) = 𝔐([Γ(N)]).base` by `H ≤ GL₂(ℤ/N)` acting through
`gammaHAut`. By KM 7.4.2 + 8.1.5 this is the coarse moduli scheme `M([Γ(N)]/H)`. -/
noncomputable def YHCoarse (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))
    (hinv : IsUnit (N : R))
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N))) : Scheme.{u} :=
  haveI : (gammaFullNaiveProblem R N).IsRepresentable :=
    (gammaFullNaive_rigid_and_representable R N hN hinv).2
  haveI : IsAffineHom (Functor.reprX (gammaFullNaiveProblem R N)).structMap :=
    ModuliProblem.gammaFullNaive_isAffineHom_structMap N hN hinv
      (Functor.representableBy _)
  (Functor.representableBy (gammaFullNaiveProblem R N)).coarseQuotient
    (gammaHAut R N H)

/-- **`Y₀(N)` over `R`** (KM 7.4.2(4) + 8.1.1; Loeffler §3.6): the coarse modular
curve at the Borel subgroup. -/
noncomputable def YZeroCoarse (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))
    (hinv : IsUnit (N : R)) : Scheme.{u} :=
  YHCoarse (R := R) N hN hinv (borel N)

/-- The chosen semi-Borel quotient-problem datum (the `Y₁`-datum of record;
KM 7.4.2(3) `[Γ₁(N)] = [Γ(N)]/{(1 ∗; 0 ∗)}`). -/
noncomputable def semiBorelQPD (N : ℕ) [NeZero N] (hN4 : 4 ≤ N)
    (hinv : IsUnit (N : R)) :
    ModuliProblem.QuotientProblemData (gammaHAut R N (semiBorel N)) :=
  (gammaH_semiBorel_closure R N hN4 (semiBorel N) le_rfl hinv).1.some

/-- The representing object of the semi-Borel quotient problem (the fine `Y₁`-object). -/
noncomputable def xOneFine (N : ℕ) [NeZero N] (hN4 : 4 ≤ N)
    (hinv : IsUnit (N : R)) : EllObj R :=
  haveI : (semiBorelQPD (R := R) N hN4 hinv).prob.IsRepresentable :=
    (gammaH_semiBorel_closure R N hN4 (semiBorel N) le_rfl hinv).2 _
  Functor.reprX (semiBorelQPD (R := R) N hN4 hinv).prob

/-- The chosen representation of the semi-Borel quotient problem by `xOneFine`. -/
noncomputable def xOneFineRepr (N : ℕ) [NeZero N] (hN4 : 4 ≤ N)
    (hinv : IsUnit (N : R)) :
    (semiBorelQPD (R := R) N hN4 hinv).prob.RepresentableBy
      (xOneFine (R := R) N hN4 hinv) :=
  haveI : (semiBorelQPD (R := R) N hN4 hinv).prob.IsRepresentable :=
    (gammaH_semiBorel_closure R N hN4 (semiBorel N) le_rfl hinv).2 _
  Functor.representableBy _

/-- **The fine modular curve `Y₁(N)` over `R`** (`N ≥ 4` invertible): the base of the
representing object of the semi-Borel quotient problem `[Γ(N)]/{(1 ∗; 0 ∗)}`
(KM 7.4.2(3): "[Γ₁(N)] … the quotient of [Γ(N)] by the 'semi-Borel' subgroup";
existence + representability = `gammaH_semiBorel_closure`, v10.349). -/
noncomputable def YOneFine (N : ℕ) [NeZero N] (hN4 : 4 ≤ N)
    (hinv : IsUnit (N : R)) : Scheme.{u} :=
  (xOneFine (R := R) N hN4 hinv).base

/-- The representing object of the full-level problem (the fine `Y(N)`-object). -/
noncomputable def xFullNaive (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))
    (hinv : IsUnit (N : R)) : EllObj R :=
  haveI : (gammaFullNaiveProblem R N).IsRepresentable :=
    (gammaFullNaive_rigid_and_representable R N hN hinv).2
  Functor.reprX (gammaFullNaiveProblem R N)

/-- The chosen representation of the full-level problem by `xFullNaive`. -/
noncomputable def xFullNaiveRepr (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))
    (hinv : IsUnit (N : R)) :
    (gammaFullNaiveProblem R N).RepresentableBy (xFullNaive (R := R) N hN hinv) :=
  haveI : (gammaFullNaiveProblem R N).IsRepresentable :=
    (gammaFullNaive_rigid_and_representable R N hN hinv).2
  Functor.representableBy _

/-- The fine projection at the `Ell/R`-level: the Yoneda-classified image of the
problem projection `[Γ(N)] ⟶ [Γ(N)]/semiBorel` at the universal full level
structure. -/
noncomputable def piOneFineEll (N : ℕ) [NeZero N] (hN4 : 4 ≤ N)
    (hinv : IsUnit (N : R)) :
    xFullNaive (R := R) N (by exact_mod_cast Nat.le_of_succ_le hN4) hinv ⟶
      xOneFine (R := R) N hN4 hinv :=
  (xOneFineRepr (R := R) N hN4 hinv).homEquiv.symm
    ((semiBorelQPD (R := R) N hN4 hinv).proj.app
      (Opposite.op (xFullNaive (R := R) N (by exact_mod_cast Nat.le_of_succ_le hN4)
        hinv))
      ((xFullNaiveRepr (R := R) N (by exact_mod_cast Nat.le_of_succ_le hN4)
        hinv).homEquiv (𝟙 _)))

/-- **The fine projection `Y(N) ⟶ Y₁(N)`** (KM 7.4.2(3)'s map `(P,Q) ↦ P` at the
scheme level). -/
noncomputable def piOneFine (N : ℕ) [NeZero N] (hN4 : 4 ≤ N)
    (hinv : IsUnit (N : R)) :
    (xFullNaive (R := R) N (by exact_mod_cast Nat.le_of_succ_le hN4) hinv).base ⟶
      YOneFine (R := R) N hN4 hinv :=
  (piOneFineEll (R := R) N hN4 hinv).baseHom

/-- The classified projection coequalizes the semi-Borel action at the `Ell/R`-level
(Yoneda transport of `proj_invariant`). -/
theorem gammaHAut_inv_comp_piOneFineEll (N : ℕ) [NeZero N] (hN4 : 4 ≤ N)
    (hinv : IsUnit (N : R)) (γ : (semiBorel N)) :
    ((xFullNaiveRepr (R := R) N (by exact_mod_cast Nat.le_of_succ_le hN4)
        hinv).autMulHom (gammaHAut R N (semiBorel N) γ)).inv ≫
      piOneFineEll (R := R) N hN4 hinv = piOneFineEll (R := R) N hN4 hinv := by
  classical
  apply (xOneFineRepr (R := R) N hN4 hinv).homEquiv.injective
  rw [(xOneFineRepr (R := R) N hN4 hinv).homEquiv_comp, piOneFineEll,
    Equiv.apply_symm_apply, ← NatTrans.naturality_apply
      (semiBorelQPD (R := R) N hN4 hinv).proj]
  have h2 : (gammaFullNaiveProblem R N).map
      (((xFullNaiveRepr (R := R) N (by exact_mod_cast Nat.le_of_succ_le hN4)
        hinv).autMulHom (gammaHAut R N (semiBorel N) γ)).inv).op
      ((xFullNaiveRepr (R := R) N (by exact_mod_cast Nat.le_of_succ_le hN4)
        hinv).homEquiv (𝟙 _)) =
      (gammaHAut R N (semiBorel N) γ).inv.app _
        ((xFullNaiveRepr (R := R) N (by exact_mod_cast Nat.le_of_succ_le hN4)
          hinv).homEquiv (𝟙 _)) := by
    have hchar := (xFullNaiveRepr (R := R) N
      (by exact_mod_cast Nat.le_of_succ_le hN4) hinv).homEquiv_comp_transportHom
      (gammaHAut R N (semiBorel N) γ).inv (𝟙 _)
    rw [Category.id_comp] at hchar
    rw [← hchar, ← (xFullNaiveRepr (R := R) N
      (by exact_mod_cast Nat.le_of_succ_le hN4) hinv).homEquiv_comp]
    rfl
  rw [h2]
  have h3 : (gammaHAut R N (semiBorel N) γ).inv =
      (gammaHAut R N (semiBorel N) γ⁻¹).hom := by
    rw [map_inv]; rfl
  have h4 := congrArg (fun (m : gammaFullNaiveProblem R N ⟶
      (semiBorelQPD (R := R) N hN4 hinv).prob) =>
    m.app (Opposite.op (xFullNaive (R := R) N
      (by exact_mod_cast Nat.le_of_succ_le hN4) hinv))
      ((xFullNaiveRepr (R := R) N (by exact_mod_cast Nat.le_of_succ_le hN4)
        hinv).homEquiv (𝟙 _)))
    ((semiBorelQPD (R := R) N hN4 hinv).proj_invariant γ⁻¹)
  rw [h3]
  exact h4

/-- **The fine projection coequalizes the transported semi-Borel action on `Y(N)`**
(the scheme-level invariance feeding the coarse universal property). -/
theorem baseSchemeAction_comp_piOneFine (N : ℕ) [NeZero N] (hN4 : 4 ≤ N)
    (hinv : IsUnit (N : R)) (γ : (semiBorel N)) :
    ((xFullNaiveRepr (R := R) N (by exact_mod_cast Nat.le_of_succ_le hN4)
        hinv).baseSchemeAction (gammaHAut R N (semiBorel N))).hom γ ≫
      piOneFine (R := R) N hN4 hinv = piOneFine (R := R) N hN4 hinv :=
  congrArg EllHom.baseHom (gammaHAut_inv_comp_piOneFineEll (R := R) N hN4 hinv γ)

end ModularCurves
