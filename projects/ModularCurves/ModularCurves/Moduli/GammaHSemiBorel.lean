/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.Moduli.GammaHMaster
import ModularCurves.Moduli.KeystoneGeometricPoint

/-!
# Γ_H rigidity for semi-Borel level subgroups, and the Borel no-go

**KM 7.4.2(3) (print p. 198, verbatim):** "The natural map `[Γ(N)] → [Γ₁(N)]`,
`(P,Q) ↦ P` identifies `[Γ₁(N)]` with the quotient of `[Γ(N)]` by the "semi-Borel"
sub-group `(1 *; 0 *)` of `GL(2, ℤ/Nℤ)`."

**Loeffler, Prop 3.8.3 (verbatim):** "`𝒫_H` is rigid on `Ell/R[1/6]` if and only if
the preimage in `SL₂(ℤ)` of `H ∩ SL₂(ℤ/N)` contains no elements of finite order
(i.e. has no elliptic points and does not contain `−1`)."

This file supplies the honest per-`H` rigidity input of `gammaH_rigidNoeth` — the
k̄-orbit-freeness `hfree` — for every `H` contained in the semi-Borel subgroup
`{(1 *; 0 *)}` (the stabilizer of the first basis vector), `N ≥ 4` invertible: a
`γ`-twisted fixed point forces the base-identical iso `e` to fix the *first* section
of the naive full level structure (the first column of `γ` is `e₁`), that section has
exact order `N` over `k̄`, and the PROVEN exact-order keystone
(`aut_endo_eq_one_of_fixes_point`, with `hbound` discharged by `hbound_of_kvc` exactly
as in the Γ₁ closure) forces `e = refl`. For such `H` the preimage of
`H ∩ SL₂(ℤ/N)` is (conjugate into) `Γ₁(N)`, torsion-free for `N ≥ 4` — the Loeffler
3.8.3 condition holds, and `P_H` is representable through the KM 4.7.0 engine.

**The Borel no-go (v10.345-AMEND §A).** For `H` containing `−1` — the Borel
`{(* *; 0 *)}` of `[Γ₀(N)]` in particular — rigidity FAILS (Loeffler 3.8.3: `−1` is a
finite-order element of the preimage), and the former `hH` finite-order pin of
`gammaH_representable_of_orderOf` is refutable inside the library: `e := negIso` is a
nontrivial base-identical iso with `isoPow e 2 = refl`, and `orderOf (−1) = 2`. The
`hH_refuted_of_neg_one_mem` witness below records this no-go as a theorem so that no
future worker attempts a fine `Y₀(N)` through the `orderOf` interface. `Y₀(N)` is the
KM Ch. 8 *coarse* moduli scheme (KM 8.1.5: `M(𝒫)/G ≅ M(𝒫/G)`; Loeffler Def 3.6.2:
`Y₀(N) = Y₁(N)/(ℤ/N)ˣ`) — a separate stream (M3).
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

/-- Local η (unit of the pointwise hom-group) — do NOT `open MonObj` here: this file
has `γ` binders and mathlib's `Monoidal/Mod.lean` puts a scoped `notation "γ"` in
`MonObj` (the v10.343 clash). Same idiom as `GammaHMaster.lean`. -/
local notation "η[" M "]" => CategoryTheory.MonObj.one (X := M)

universe u

namespace ModularCurves

variable (R : CommRingCat.{u})

/-! ## The semi-Borel subgroup -/

/-- The **semi-Borel subgroup** `{(1 *; 0 *)} ≤ GL₂(ℤ/N)` (KM 7.4.2(3)): matrices
whose first column is `e₁`. Under the `glSmul` right-action convention
(`g • (P,Q) = (g₀₀P + g₁₀Q, g₀₁P + g₁₁Q)`) these are exactly the elements fixing the
first component of every full level structure. `[Γ(N)]`-quotient by it = `[Γ₁(N)]`
(KM 7.4.2(3)). -/
def semiBorel (N : ℕ) [NeZero N] :
    Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0 = 1 ∧
    (g : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0 = 0}
  mul_mem' := by
    rintro a b ⟨ha00, ha10⟩ ⟨hb00, hb10⟩
    constructor
    · show ((a : Matrix (Fin 2) (Fin 2) (ZMod N)) * b) 0 0 = 1
      rw [Matrix.mul_apply, Fin.sum_univ_two, ha00, hb00, hb10, one_mul, mul_zero, add_zero]
    · show ((a : Matrix (Fin 2) (Fin 2) (ZMod N)) * b) 1 0 = 0
      rw [Matrix.mul_apply, Fin.sum_univ_two, ha10, hb10, zero_mul, mul_zero, add_zero]
  one_mem' := by
    constructor
    · show (1 : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0 = 1
      simp
    · show (1 : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0 = 0
      simp
  inv_mem' := by
    rintro g ⟨h00, h10⟩
    -- entries of the inverse from `g * g⁻¹ = 1` and unit-ness of `det g = g 1 1`
    have hmul : (g : Matrix (Fin 2) (Fin 2) (ZMod N)) *
        ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
          Matrix (Fin 2) (Fin 2) (ZMod N)) = 1 := g.mul_inv
    have h11 : IsUnit ((g : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 1) := by
      have hdet : IsUnit (g : Matrix (Fin 2) (Fin 2) (ZMod N)).det :=
        (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
      rwa [Matrix.det_fin_two, h00, h10, one_mul, mul_zero, sub_zero] at hdet
    have e10 : ((g : Matrix (Fin 2) (Fin 2) (ZMod N)) *
        ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
          Matrix (Fin 2) (Fin 2) (ZMod N))) 1 0 = 0 := by
      rw [hmul]; simp
    have e00 : ((g : Matrix (Fin 2) (Fin 2) (ZMod N)) *
        ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
          Matrix (Fin 2) (Fin 2) (ZMod N))) 0 0 = 1 := by
      rw [hmul]; simp
    rw [Matrix.mul_apply, Fin.sum_univ_two, h10, zero_mul, zero_add] at e10
    have hB10 : ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
        Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0 = 0 :=
      (IsUnit.mul_right_eq_zero h11).mp e10
    rw [Matrix.mul_apply, Fin.sum_univ_two, h00, one_mul, hB10, mul_zero, add_zero] at e00
    exact ⟨e00, hB10⟩

/-- Membership in the semi-Borel subgroup, unfolded. -/
theorem mem_semiBorel_iff (N : ℕ) [NeZero N]
    (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    g ∈ semiBorel N ↔ (g : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0 = 0 :=
  Iff.rfl

/-! ## Semi-Borel matrices fix the first component of a full level structure -/

variable {S : Scheme.{u}}

/-- A semi-Borel matrix fixes the first component of every full level structure:
`(glSmul g L).1.1 = (1.val : ℤ) • L.1.1 + (0.val : ℤ) • L.1.2 = L.1.1` (needs
`1 < N` so that `(1 : ZMod N).val = 1`). -/
theorem EllipticCurve.glSmul_fst_of_mem_semiBorel (E : EllipticCurve S) {N : ℕ}
    [NeZero N] (hN : 1 < N) (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
    (hg : g ∈ semiBorel N) (L : E.FullLevelPt N) :
    (E.glSmul g L).1.1 = L.1.1 := by
  show (((g : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0).val : ℤ) • L.1.1
      + (((g : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0).val : ℤ) • L.1.2 = L.1.1
  rw [hg.1, hg.2, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hN, ZMod.val_zero,
    Nat.cast_one, Nat.cast_zero, one_smul, zero_smul, add_zero]

/-- **The untwist + first-component extraction**: a `γ`-twisted fixed point of the
naive full-level problem under a base-identical iso `e`, for `γ ∈ H ≤ semi-Borel`,
forces `e` to fix the first section of the structure:
`(gammaHAut γ).app (map e.op b) = b` untwists (via `gammaHAut_app_val` and
`glSmul_mul`) to `map e.op b = glSmul γ b`, whose first components read
`pullSection e b.1.1 = b.1.1`. Mirror of the untwist in
`gammaH_hfree_of_orderOf_absurd` + the `h1`-extraction of
`gammaFullNaive_twist_pow_refl`. -/
theorem gammaFullNaive_fix_fst_of_le_semiBorel (N : ℕ) [NeZero N] (hN : 1 < N)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hle : H ≤ semiBorel N)
    (k : Type u) [Field k] [IsAlgClosed k]
    (sm : Spec (CommRingCat.of k) ⟶ Spec R)
    (E : EllipticCurve (Spec (CommRingCat.of k)))
    (e : (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R) ≅
      (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R))
    (b : (gammaFullNaiveProblem R N).obj
      (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R)))
    (γ : ↥H)
    (hcon : (gammaHAut R N H γ).hom.app
      (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R))
      ((gammaFullNaiveProblem R N).map e.hom.op b) = b) :
    EllHom.pullSection R e.hom b.1.1 = b.1.1 := by
  rw [gammaHAut_app_val] at hcon
  have hcon2 := congrArg
    (E.glSmul (((γ⁻¹ : ↥H) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))⁻¹) hcon
  rw [← E.glSmul_mul, mul_inv_cancel, E.glSmul_one] at hcon2
  have hu : (((γ⁻¹ : ↥H) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))⁻¹
      = (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) := by
    rw [show (((γ⁻¹ : ↥H) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
        = ((γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))⁻¹ from rfl, inv_inv]
  rw [hu] at hcon2
  have h1 : EllHom.pullSection R e.hom b.1.1 =
      (E.glSmul ((γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))) b).1.1 :=
    congrArg (fun z => z.1.1) hcon2
  exact h1.trans (E.glSmul_fst_of_mem_semiBorel hN _ (hle γ.2) b)

/-- Over `k̄` with `N` invertible, the first section of a naive full level structure
has exact order `N`: its small multiples are nonzero. (The structure pins a basis of
`E[N](k̄) ≅ (ℤ/N)²` — the [GH2-core] geometric-fibre machinery
(`torsion_geometricFibre_rank_two`); a basis vector of `(ℤ/N)²` has additive order
`N`.) -/
theorem gammaFullNaive_fst_smul_ne_zero (N : ℕ) [NeZero N]
    (hinv : IsUnit (N : R))
    (k : Type u) [Field k] [IsAlgClosed k]
    (sm : Spec (CommRingCat.of k) ⟶ Spec R)
    (E : EllipticCurve (Spec (CommRingCat.of k)))
    (b : (gammaFullNaiveProblem R N).obj
      (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R)))
    (a : ℕ) (ha0 : 0 < a) (haN : a < N) :
    (a : ℤ) • b.1.1 ≠ 0 := by
  intro hzero
  have hN2 : 2 ≤ N := by omega
  haveI : Fact (1 < N) := ⟨by omega⟩
  -- `N` is invertible in `k` along `sm`
  have hNk : (N : k) ≠ 0 := by
    have hinvk : IsUnit ((N : ℕ) : k) := by
      have h := hinv.map (Spec.preimage sm).hom
      rwa [map_natCast] at h
    exact hinvk.ne_zero
  -- torsion facts for the two sections (points at `t = 𝟙`)
  have hppN : (N : ℤ) • b.1.1 = 0 := b.2.1.1
  have hpqN : (N : ℤ) • b.1.2 = 0 := b.2.1.2
  -- the rank-two basis at the base point itself
  obtain ⟨φ⟩ := E.torsion_geometricFibre_rank_two N k (𝟙 (Spec (CommRingCat.of k))) hNk
  set M := Submodule.torsionBy ℤ (E.Point (𝟙 (Spec (CommRingCat.of k)))) (N : ℤ) with hMdef
  have hppM : b.1.1 ∈ M := (Submodule.mem_torsionBy_iff _ _).mpr hppN
  have hpqM : b.1.2 ∈ M := (Submodule.mem_torsionBy_iff _ _).mpr hpqN
  have hmem : ∀ c : Fin 2 → ZMod N,
      ((c 0).val : ℤ) • b.1.1 + ((c 1).val : ℤ) • b.1.2 ∈ M := fun c =>
    add_mem (M.smul_mem _ hppM) (M.smul_mem _ hpqM)
  set S : (Fin 2 → ZMod N) → M :=
    fun c => ⟨((c 0).val : ℤ) • b.1.1 + ((c 1).val : ℤ) • b.1.2, hmem c⟩ with hS
  -- surjectivity from the full-level generation clause at `t = 𝟙`
  have hSsurj : Function.Surjective S := by
    intro w
    have hwN : (N : ℤ) • (w : E.Point (𝟙 (Spec (CommRingCat.of k)))) = 0 := by
      have := w.2; rwa [Submodule.mem_torsionBy_iff] at this
    have hwmem : (w : E.Point (𝟙 (Spec (CommRingCat.of k)))) ∈
        AddSubgroup.closure {b.1.1, b.1.2} :=
      b.2.2 k (𝟙 (Spec (CommRingCat.of k))) (w : E.Point (𝟙 (Spec (CommRingCat.of k)))) hwN
    rw [AddSubgroup.mem_closure_pair] at hwmem
    obtain ⟨j, l, hjl⟩ := hwmem
    refine ⟨![(j : ZMod N), (l : ZMod N)], ?_⟩
    apply Subtype.ext
    simp only [hS, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [EllipticCurve.zsmul_eq_of_intCast_eq b.1.1 hppN (a := (((j : ZMod N)).val : ℤ))
          (b := j) (by simp [ZMod.natCast_val]),
        EllipticCurve.zsmul_eq_of_intCast_eq b.1.2 hpqN (a := (((l : ZMod N)).val : ℤ))
          (b := l) (by simp [ZMod.natCast_val])]
    exact hjl
  have hSinj : Function.Injective S :=
    (Finite.injective_iff_surjective_of_equiv φ.symm.toEquiv).mpr hSsurj
  -- `S ![a, 0] = S ![0, 0]` from the vanishing, so `(a : ZMod N) = 0`, so `N ∣ a`
  have hSa : S ![(a : ZMod N), 0] = S ![0, 0] := by
    apply Subtype.ext
    simp only [hS, Matrix.cons_val_zero, Matrix.cons_val_one,
      ZMod.val_zero, Nat.cast_zero, zero_smul, add_zero]
    rw [EllipticCurve.zsmul_eq_of_intCast_eq b.1.1 hppN (a := (((a : ZMod N)).val : ℤ))
          (b := (a : ℤ)) (by simp [ZMod.natCast_val])]
    exact hzero
  have hcast : ((a : ZMod N)) = 0 := by
    have := congrFun (hSinj hSa) 0
    simpa using this
  have hdvd : N ∣ a := (CharP.cast_eq_zero_iff (ZMod N) N a).mp hcast
  have := Nat.le_of_dvd ha0 hdvd
  omega

/-- **The naive-side one-section rigidity kill** (the `gammaOneDrinfeld_fix_absurd`
endgame on the naive full-level problem): over `k̄`, `N ≥ 4` invertible, a
base-identical iso `e ≠ refl` cannot fix a section of exact order `N`. Route: `e`
transports to a pointed endomorphism `εO` of `E.asOver` (invertible since `e` is an
iso), the fixed section is `εO`-fixed, its small multiples are nonzero
(`gammaFullNaive_fst_smul_ne_zero`), and the PROVEN keystone
`aut_endo_eq_one_of_fixes_point` — `hbound` discharged by `hbound_of_kvc` exactly as
in the Γ₁ closure (`gammaOneDrinfeld_rigid_and_representable`) — forces `εO = 𝟙`,
hence `e.hom.top = 𝟙` and `e = refl`. -/
theorem gammaFullNaive_fix_fst_absurd (N : ℕ) [NeZero N] (hN : 4 ≤ N)
    (hinv : IsUnit (N : R))
    (k : Type u) [Field k] [IsAlgClosed k]
    (sm : Spec (CommRingCat.of k) ⟶ Spec R)
    (E : EllipticCurve (Spec (CommRingCat.of k)))
    (e : (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R) ≅
      (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R))
    (he : e.hom.baseHom = 𝟙 _) (hne : e ≠ Iso.refl _)
    (b : (gammaFullNaiveProblem R N).obj
      (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R)))
    (hfix : EllHom.pullSection R e.hom b.1.1 = b.1.1) : False := by
  classical
  set c := e.hom.top with hc
  -- the fixed section is `c`-fixed
  have hPc : b.1.1.1 ≫ c = b.1.1.1 := by
    have hlf : (EllHom.pullSection R e.hom b.1.1).1 ≫ e.hom.top
        = e.hom.baseHom ≫ b.1.1.1 := e.hom.isPullback.lift_fst _ _ _
    rw [hfix, he, Category.id_comp] at hlf
    exact hlf
  -- `c` as a pointed `Over`-endomorphism
  have hcπ : c ≫ E.π = E.π := by
    have h := e.hom.isPullback.w
    rw [he, Category.comp_id] at h
    exact h
  set εO : E.asOver ⟶ E.asOver := Over.homMk c hcπ with hεO
  have hzc : E.zero ≫ c = E.zero := by
    have h := e.hom.zero_w
    rw [he, Category.id_comp] at h
    exact h
  have hη : η[E.asOver] ≫ εO = η[E.asOver] := by
    refine Over.OverMorphism.ext ?_
    show (η[E.asOver]).left ≫ c = (η[E.asOver]).left
    rw [E.one_eq_zero]
    have s1 : ((𝟙_ (Over (Spec (CommRingCat.of k)))).hom ≫ E.zero) ≫ c
        = (𝟙_ (Over (Spec (CommRingCat.of k)))).hom ≫ E.zero ≫ c := Category.assoc _ _ _
    have s2 : (𝟙_ (Over (Spec (CommRingCat.of k)))).hom ≫ E.zero ≫ c
        = (𝟙_ (Over (Spec (CommRingCat.of k)))).hom ≫ E.zero :=
      congrArg (fun mm => (𝟙_ (Over (Spec (CommRingCat.of k)))).hom ≫ mm) hzc
    exact s1.trans s2
  -- `εO` is invertible (from the iso `e`)
  haveI hIsoε : IsIso εO := by
    have hcπ' : e.inv.top ≫ E.π = E.π := by
      have h := e.inv.isPullback.w
      rw [EllObj.isoInv_baseHom e he, Category.comp_id] at h
      exact h
    exact ⟨Over.homMk e.inv.top hcπ',
      Over.OverMorphism.ext (congrArg EllHom.top e.hom_inv_id),
      Over.OverMorphism.ext (congrArg EllHom.top e.inv_hom_id)⟩
  -- the small multiples of the fixed section are nonzero (naive order supply)
  have hP2 : (2 : ℤ) • b.1.1 ≠ 0 := by
    have h := gammaFullNaive_fst_smul_ne_zero R N hinv k sm E b 2 (by norm_num) (by omega)
    simpa using h
  have hP3 : (3 : ℤ) • b.1.1 ≠ 0 := by
    have h := gammaFullNaive_fst_smul_ne_zero R N hinv k sm E b 3 (by norm_num) (by omega)
    simpa using h
  -- the equiv-form fix, and the KVC single-point kill
  have hfix' : (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) b.1.1 ≫ εO
      = (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) b.1.1 := by
    refine Over.OverMorphism.ext ?_
    show b.1.1.1 ≫ c = b.1.1.1
    exact hPc
  have hεid : εO = 𝟙 E.asOver :=
    EllipticCurve.pointedAuto_eq_id_of_fixes_point_kvc E εO hIsoε hη b.1.1 hP2 hP3 hfix'
  have hcid : c = 𝟙 E.E := congrArg CommaMorphism.left hεid
  exact hne (Iso.ext (EllHom.ext he hcid))

/-! ## The hfree pin for `H ≤ semiBorel`, and the closure -/

/-- **[Γ_H hfree, semi-Borel] (the rectified Gate 2)** — the `hfree` pin of
`gammaH_rigidNoeth` holds for every `H` contained in the semi-Borel subgroup,
`N ≥ 4` invertible: assembly of `gammaFullNaive_fix_fst_of_le_semiBorel` +
`gammaFullNaive_fix_fst_absurd`. -/
theorem gammaH_hfree_of_le_semiBorel (N : ℕ) [NeZero N] (hN : 4 ≤ N)
    (hinv : IsUnit (N : R))
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hle : H ≤ semiBorel N)
    (k : Type u) [Field k] [IsAlgClosed k]
    (sm : Spec (CommRingCat.of k) ⟶ Spec R)
    (E : EllipticCurve (Spec (CommRingCat.of k)))
    (e : (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R) ≅
      (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R))
    (he : e.hom.baseHom = 𝟙 _) (hne : e ≠ Iso.refl _)
    (b : (gammaFullNaiveProblem R N).obj
      (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R)))
    (γ : ↥H) :
    (gammaHAut R N H γ).hom.app
      (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R))
      ((gammaFullNaiveProblem R N).map e.hom.op b) ≠ b := by
  intro hcon
  exact gammaFullNaive_fix_fst_absurd R N hN hinv k sm E e he hne b
    (gammaFullNaive_fix_fst_of_le_semiBorel R N (by omega) H hle k sm E e b γ hcon)

/-- **[Γ_H rigidity, semi-Borel, noetherian-local]** — `P_H` is noetherian-locally
rigid for every `H ≤ semiBorel N`, `N ≥ 4` invertible, UNCONDITIONALLY (no `hH`/`hfree`
pin left): `gammaH_rigidNoeth` fed by `gammaH_hfree_of_le_semiBorel`. -/
theorem gammaH_rigidNoeth_of_le_semiBorel (N : ℕ) [NeZero N] (hN : 4 ≤ N)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hle : H ≤ semiBorel N)
    (hinv : IsUnit (N : R))
    (qpd : ModuliProblem.QuotientProblemData (gammaHAut R N H)) :
    qpd.prob.RigidNoeth := by
  refine gammaH_rigidNoeth R N (by exact_mod_cast Nat.le_of_lt_succ (by omega)) H hinv qpd ?_
  intro k _ _ sm E e he hne b γ
  exact gammaH_hfree_of_le_semiBorel R N hN hinv H hle k sm E e he hne b γ

/-- **[Γ_H `.Representable`, semi-Borel] (KM 7.4.2(3)-adjacent; the first
unconditional representable `Y_H` beyond `H = ⊥`)** — for `H ≤ semiBorel N`,
`N ≥ 4` invertible, the quotient problem `P_H` is representable: relative
representability and affineness from `qpd`, rigidity from
`gammaH_rigidNoeth_of_le_semiBorel`, through the KM 4.7.0 engine (mirror of
`gammaH_representable_of_orderOf` with the honest rigidity input). With the
M1-unconditional `gammaH_relativelyRepresentable` this closes `Y_H(N)` for every
semi-Borel `H`; by KM 7.4.2(3) the `H = semiBorel` quotient is `[Γ₁(N)]` itself. -/
theorem gammaH_representable_of_le_semiBorel (N : ℕ) [NeZero N] (hN : 4 ≤ N)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hle : H ≤ semiBorel N)
    (hinv : IsUnit (N : R))
    (qpd : ModuliProblem.QuotientProblemData (gammaHAut R N H)) :
    qpd.prob.Representable :=
  ModuliProblem.representable_of_affineOverEll_of_rigidNoeth qpd.prob qpd.affineOverEll
    qpd.affineOverEll.relativelyRepresentable
    (gammaH_rigidNoeth_of_le_semiBorel R N hN H hle hinv qpd)

/-- **[Y_H HEADLINE, semi-Borel] (KM 7.4.2(3)-grade)** — for `N ≥ 4` invertible and any
`H ≤ semiBorel N`, the quotient problem data exists UNCONDITIONALLY (M1's
diagonal-free `gammaH_relativelyRepresentable`) and every such quotient problem is
representable (`gammaH_representable_of_le_semiBorel`). The first unconditional
`Y_H(N)` beyond `H = ⊥`; at `H = semiBorel N` the quotient is `[Γ₁(N)]` itself
(KM 7.4.2(3)). -/
theorem gammaH_semiBorel_closure (N : ℕ) [NeZero N] (hN : 4 ≤ N)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hle : H ≤ semiBorel N)
    (hinv : IsUnit (N : R)) :
    Nonempty (ModuliProblem.QuotientProblemData (gammaHAut R N H)) ∧
      ∀ qpd : ModuliProblem.QuotientProblemData (gammaHAut R N H),
        qpd.prob.Representable :=
  ⟨gammaH_relativelyRepresentable R N H hinv,
    fun qpd => gammaH_representable_of_le_semiBorel R N hN H hle hinv qpd⟩

/-! ## The Borel no-go: the `orderOf` pin is refutable for `−1 ∈ H` -/

/-- `−1` has order two in `GL₂(ℤ/N)` for `N ≥ 3`. -/
theorem orderOf_neg_one_gl (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    orderOf (-1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime (by rw [neg_one_sq]) ?_
  intro hcon
  have hval : ((-1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
      Matrix (Fin 2) (Fin 2) (ZMod N)) = ((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
      Matrix (Fin 2) (Fin 2) (ZMod N)) := congrArg Units.val hcon
  have hentry := congrFun (congrFun hval 0) 0
  rw [Units.val_neg, Units.val_one] at hentry
  have h2 : (2 : ZMod N) = 0 := by
    have : (-1 : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0 = -1 := by simp
    rw [this] at hentry
    have h1 : (1 : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0 = 1 := by simp
    rw [h1] at hentry
    have := congrArg (· + 1) hentry
    simpa [neg_add_cancel, one_add_one_eq_two] using this.symm
  have hdvd : N ∣ 2 := by
    have := (CharP.cast_eq_zero_iff (ZMod N) N 2).mp (by exact_mod_cast h2)
    exact this
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- The square of the negation iso is the identity (already `negHom_comp_negHom`,
iterated through `isoPow`). -/
theorem isoPow_negIso_two (X : EllObj R) :
    isoPow (EllObj.negIso R X) 2 = Iso.refl X := by
  refine Iso.ext ?_
  show (isoPow (EllObj.negIso R X) 1 ≪≫ EllObj.negIso R X).hom = _
  show (isoPow (EllObj.negIso R X) 0 ≪≫ EllObj.negIso R X ≪≫ EllObj.negIso R X).hom = _
  show (Iso.refl X ≪≫ EllObj.negIso R X ≪≫ EllObj.negIso R X).hom = _
  rw [Iso.trans_hom, Iso.trans_hom, Iso.refl_hom, Category.id_comp]
  exact EllObj.negHom_comp_negHom R X

/-- Over a base with a geometric point, the negation iso is not the identity
(T-H7c `mulByHom_neg_one_ne_id`, lifted to the `Ell/R`-iso). -/
theorem negIso_ne_refl (X : EllObj R) (k : Type u) [Field k] [IsAlgClosed k]
    (t : Spec (CommRingCat.of k) ⟶ X.base) :
    EllObj.negIso R X ≠ Iso.refl X := by
  intro hEq
  have htop : (EllObj.negIso R X).hom.top = (Iso.refl X).hom.top :=
    congrArg (fun i => i.hom.top) hEq
  exact X.curve.mulByHom_neg_one_ne_id k t htop

/-- **THE BOREL NO-GO (v10.345-AMEND §A, as a theorem)** — for any `H` containing
`−1` (the Borel of `[Γ₀(N)]` in particular) and any geometric test object, the
former `hH` finite-order pin of `gammaH_representable_of_orderOf` is FALSE: the
negation iso is a nontrivial base-identical iso with
`isoPow e (orderOf γ) = refl` at `γ = −1`. Classical content: Loeffler Prop 3.8.3
(verbatim: rigid ⟺ the `SL₂(ℤ)`-preimage of `H ∩ SL₂(ℤ/N)` "has no elliptic points
and does not contain `−1`"); `[Γ₀(N)]` is a quotient problem (KM 7.4.2(4)) whose
moduli scheme is COARSE (KM 8.1). Do NOT attempt a fine `Y₀(N)` through the
`orderOf` interface. -/
theorem hH_refuted_of_neg_one_mem (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hmem : (-1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) ∈ H)
    (k : Type u) [Field k] [IsAlgClosed k]
    (sm : Spec (CommRingCat.of k) ⟶ Spec R)
    (E : EllipticCurve (Spec (CommRingCat.of k))) :
    ∃ (e : (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R) ≅
        (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R)),
      e.hom.baseHom = 𝟙 _ ∧ e ≠ Iso.refl _ ∧ ∃ γ : ↥H,
        isoPow e (orderOf ((γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))) =
          Iso.refl _ := by
  refine ⟨EllObj.negIso R (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R), rfl,
    negIso_ne_refl R _ k (𝟙 _), ⟨(-1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)), hmem⟩, ?_⟩
  rw [show (((⟨(-1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)), hmem⟩ : ↥H) :
      Matrix.GeneralLinearGroup (Fin 2) (ZMod N))) =
      (-1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) from rfl,
    orderOf_neg_one_gl N hN]
  exact isoPow_negIso_two R _

end ModularCurves
