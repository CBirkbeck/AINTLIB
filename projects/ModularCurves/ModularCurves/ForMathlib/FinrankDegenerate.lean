/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Fibre rank vanishes for morphisms factoring through a Cartier-type subscheme

`Scheme.Hom.finrank f x` (mathlib's fibre rank of `f : X ⟶ C` at `x : C`) is `0` whenever `f`
factors through the subscheme of an ideal sheaf `J` that contains, on some affine open around
`x`, a **nonzerodivisor** — e.g. the ideal of a section of a smooth relative curve (a relative
effective Cartier divisor).

No flatness or finiteness of `f` is assumed. The mechanism: the pushforward algebra of `f`
over the canonical chart at `x` is killed by the (pulled-back) ideal, while the ideal-sheaf
compatibilities supply an ideal element over the chart with **nonzero germ** at `x`; a module
with a nonzero annihilating scalar has `rankAtStalk` zero (torsion has no free rank). This
computes the degree of the constant endomorphism `[0]` of an elliptic curve (`deg [0] = 0`,
KM 2.6.1's degenerate case) with no zero-or-isogeny dichotomy.

* `Module.rankAtStalk_eq_zero_of_forall_smul_eq_zero` — the algebra core.
* `AlgebraicGeometry.Scheme.IdealSheafData.exists_mem_germ_ne_zero_of_le` — germ-filling for
  ideal sheaves along inclusions of affine opens.
* `AlgebraicGeometry.Scheme.IdealSheafData.appTop_pullback_snd_appLE_eq_zero` — the pulled
  ideal kills the pushforward algebra.
* `AlgebraicGeometry.Scheme.Hom.finrank_eq_zero_of_factors_of_nonZeroDivisor_mem` — the main
  theorem.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

/-- **Torsion has no free rank**: if a single scalar `a` kills the whole module and has
nonzero image in the localization at `p`, then the rank of `M` at the stalk of `p` is `0`.
(No finiteness or flatness of `M` is assumed.) -/
theorem Module.rankAtStalk_eq_zero_of_forall_smul_eq_zero {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (p : PrimeSpectrum R) (a : R)
    (ha : ∀ m : M, a • m = 0)
    (hp : algebraMap R (Localization.AtPrime p.asIdeal) a ≠ 0) :
    Module.rankAtStalk M p = 0 := by
  have h0 : Module.rank (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl M) = 0 := by
    rw [rank_eq_zero_iff]
    intro m
    refine ⟨algebraMap R _ a, hp, ?_⟩
    induction m using LocalizedModule.induction_on with
    | h m s =>
      rw [algebraMap_smul, LocalizedModule.smul'_mk, ha m]
      exact LocalizedModule.zero_mk s
  rw [Module.rankAtStalk, Module.finrank, h0]
  simp

namespace AlgebraicGeometry

/-- Transport `Scheme.Hom.appLE` along an equality of morphisms (the type of `appLE` does not
depend on the morphism, so this is a safe rewrite). -/
theorem Scheme.Hom.appLE_eq_of_eq {P C : Scheme.{u}} {m m' : P ⟶ C} (h : m = m')
    (U : C.Opens) (V : P.Opens) (e : V ≤ m ⁻¹ᵁ U) :
    m.appLE U V e = m'.appLE U V (h ▸ e) := by
  subst h; rfl

/-- Public defeq re-characterization of `Scheme.Hom.finrank`: the rank at `x` is the
`RingHom.finrank` of the global-sections algebra of the pullback of `f` along the canonical
affine chart at `x`, at the chart point's prime. -/
theorem Scheme.Hom.finrank_eq_rankAtStalk_chart {X C : Scheme.{u}} (f : X ⟶ C) (x : C) :
    f.finrank x =
      (Limits.pullback.snd f (C.affineOpenCover.f (C.affineOpenCover.idx x))).appTop.hom.finrank
        ((Spec (C.affineOpenCover.X (C.affineOpenCover.idx x))).isoSpec.hom
          (C.affineOpenCover.covers x).choose) := rfl

/-- A germ of a section of an ideal-sheaf component survives restriction to a smaller affine
open: if `f₀ ∈ J.ideal V` has nonzero germ at `x ∈ W ≤ V` with `W` affine, then some
`a ∈ J.ideal W` has nonzero germ at `x`. -/
theorem Scheme.IdealSheafData.exists_mem_germ_ne_zero_of_le {C : Scheme.{u}}
    (J : C.IdealSheafData) {W V : C.affineOpens} (hWV : W ≤ V) {x : C} (hxW : x ∈ W.1)
    (f₀ : Γ(C, V.1)) (hf₀ : f₀ ∈ J.ideal V)
    (hgerm : C.presheaf.germ V.1 x (hWV hxW) f₀ ≠ 0) :
    ∃ a ∈ J.ideal W, C.presheaf.germ W.1 x hxW a ≠ 0 := by
  refine ⟨(C.presheaf.map (homOfLE (show W.1 ≤ V.1 from hWV)).op).hom f₀, ?_, ?_⟩
  · rw [← J.map_ideal hWV]
    exact Ideal.mem_map_of_mem _ hf₀
  · simpa only [TopCat.Presheaf.germ_res_apply] using hgerm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Sections of an ideal sheaf die in the pushforward algebra of any morphism factoring
through the subscheme: for `f = g ≫ J.subschemeι` and `a ∈ J.ideal U₀`, the image of `a` in
the global sections of `pullback f u` (through the chart `u` and the pullback projection)
is zero. -/
theorem Scheme.IdealSheafData.appTop_pullback_snd_appLE_eq_zero {X C Y : Scheme.{u}}
    (f : X ⟶ C) (J : C.IdealSheafData) (g : X ⟶ J.subscheme) (hf : f = g ≫ J.subschemeι)
    (u : Y ⟶ C) (U₀ : C.affineOpens) (hle : (⊤ : Y.Opens) ≤ u ⁻¹ᵁ U₀.1)
    (a : Γ(C, U₀.1)) (ha : a ∈ J.ideal U₀) :
    (Limits.pullback.snd f u).appTop.hom (u.appLE U₀.1 ⊤ hle a) = 0 := by
  have hzero : (J.subschemeι.app U₀.1) a = 0 := by
    show (J.subschemeι.app U₀.1).hom a = 0
    rw [← RingHom.mem_ker, J.ker_subschemeι_app U₀]
    exact ha
  have h2 : Limits.pullback.snd f u ≫ u
      = (Limits.pullback.fst f u ≫ g) ≫ J.subschemeι := by
    rw [← Limits.pullback.condition, hf, Category.assoc]
  have hstep1 : u.appLE U₀.1 ⊤ hle ≫
      (Limits.pullback.snd f u).appLE ⊤ (Limits.pullback.snd f u ⁻¹ᵁ ⊤) le_rfl
      = (Limits.pullback.snd f u ≫ u).appLE U₀.1 (Limits.pullback.snd f u ⁻¹ᵁ ⊤)
          (le_rfl.trans ((TopologicalSpace.Opens.map (Limits.pullback.snd f u).base).map (homOfLE hle)).le) :=
    Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  have hstep2 : (Limits.pullback.snd f u ≫ u).appLE U₀.1 (Limits.pullback.snd f u ⁻¹ᵁ ⊤)
        (le_rfl.trans ((TopologicalSpace.Opens.map (Limits.pullback.snd f u).base).map (homOfLE hle)).le)
      = ((Limits.pullback.fst f u ≫ g) ≫ J.subschemeι).appLE U₀.1
          (Limits.pullback.snd f u ⁻¹ᵁ ⊤) (h2 ▸
            (le_rfl.trans ((TopologicalSpace.Opens.map (Limits.pullback.snd f u).base).map (homOfLE hle)).le)) :=
    Scheme.Hom.appLE_eq_of_eq h2 _ _ _
  have hstep3 : ((Limits.pullback.fst f u ≫ g) ≫ J.subschemeι).appLE U₀.1
        (Limits.pullback.snd f u ⁻¹ᵁ ⊤) (h2 ▸
          (le_rfl.trans ((TopologicalSpace.Opens.map (Limits.pullback.snd f u).base).map (homOfLE hle)).le))
      = J.subschemeι.app U₀.1 ≫ (Limits.pullback.fst f u ≫ g).appLE _
          (Limits.pullback.snd f u ⁻¹ᵁ ⊤) _ :=
    Scheme.Hom.comp_appLE _ _ _ _ _
  show (Limits.pullback.snd f u).appTop (u.appLE U₀.1 ⊤ hle a) = 0
  calc (Limits.pullback.snd f u).appTop (u.appLE U₀.1 ⊤ hle a)
      = ((Limits.pullback.snd f u).appLE ⊤ (Limits.pullback.snd f u ⁻¹ᵁ ⊤) le_rfl)
          (u.appLE U₀.1 ⊤ hle a) := by
        rw [show (Limits.pullback.snd f u).appTop = (Limits.pullback.snd f u).app ⊤ from rfl,
          Scheme.Hom.app_eq_appLE]
        rfl
    _ = (u.appLE U₀.1 ⊤ hle ≫
          (Limits.pullback.snd f u).appLE ⊤ (Limits.pullback.snd f u ⁻¹ᵁ ⊤) le_rfl) a := by
        rw [CommRingCat.comp_apply]
    _ = (J.subschemeι.app U₀.1 ≫ (Limits.pullback.fst f u ≫ g).appLE _
          (Limits.pullback.snd f u ⁻¹ᵁ ⊤) _) a := by
        rw [hstep1, hstep2, hstep3]
    _ = 0 := by rw [CommRingCat.comp_apply, hzero, map_zero]

/-- **Fibre rank vanishes on factoring through a Cartier-type subscheme.** If `f : X ⟶ C`
factors through `J.subschemeι` for an ideal sheaf `J` that contains a nonzerodivisor `f₀` on
some affine open `V ∋ x`, then `f.finrank x = 0`. No flatness/finiteness of `f` is needed:
the pushforward module is `J`-torsion while `J` has a nonzero germ at `x`. -/
theorem Scheme.Hom.finrank_eq_zero_of_factors_of_nonZeroDivisor_mem {X C : Scheme.{u}}
    (f : X ⟶ C) (J : C.IdealSheafData) (g : X ⟶ J.subscheme)
    (hf : f = g ≫ J.subschemeι) (x : C) (V : C.affineOpens) (hxV : x ∈ V.1)
    (f₀ : Γ(C, V.1)) (hf₀ : f₀ ∈ J.ideal V)
    (hnzd : f₀ ∈ nonZeroDivisors Γ(C, V.1)) :
    f.finrank x = 0 := by
  classical
  haveI : IsOpenImmersion (C.affineOpenCover.f (C.affineOpenCover.idx x)) :=
    C.affineOpenCover.map_prop _
  -- the canonical chart of the `finrank` definition; work at the chart point throughout
  set u : Spec (C.affineOpenCover.X (C.affineOpenCover.idx x)) ⟶ C :=
    C.affineOpenCover.f (C.affineOpenCover.idx x) with hu
  set w := (C.affineOpenCover.covers x).choose with hwdef
  have hw : u.base w = x := (C.affineOpenCover.covers x).choose_spec
  have hU₀ : IsAffineOpen u.opensRange := isAffineOpen_opensRange u
  set U₀ : C.affineOpens := ⟨u.opensRange, hU₀⟩ with hU₀def
  have hxV' : u.base w ∈ V.1 := hw.symm ▸ hxV
  have hxU₀ : u.base w ∈ U₀.1 := ⟨w, rfl⟩
  -- ### Step 1: the germ of `f₀` at the chart point is nonzero (nonzerodivisors on affines)
  have hgermV : C.presheaf.germ V.1 (u.base w) hxV' f₀ ≠ 0 := by
    letI := C.presheaf.algebra_section_stalk (⟨u.base w, hxV'⟩ : V.1)
    haveI := V.2.isLocalization_stalk ⟨u.base w, hxV'⟩
    intro h0
    obtain ⟨cc, hcc⟩ := (IsLocalization.map_eq_zero_iff
      (V.2.primeIdealOf ⟨u.base w, hxV'⟩).asIdeal.primeCompl
      (C.presheaf.stalk (u.base w)) f₀).mp (by exact h0)
    have hc0 : (cc : Γ(C, V.1)) = 0 := (mem_nonZeroDivisors_iff.mp hnzd).2 _ hcc
    exact cc.2 (hc0 ▸ (V.2.primeIdealOf ⟨u.base w, hxV'⟩).asIdeal.zero_mem)
  -- ### Step 2: an ideal element over a chart-basic affine `W ≤ U₀ ⊓ V` with nonzero germ
  obtain ⟨s, hsleV, hxs⟩ := U₀.2.exists_basicOpen_le (⟨u.base w, hxV'⟩ : V.1) hxU₀
  have hWV : C.affineBasicOpen s ≤ V := hsleV
  have hWU₀ : C.affineBasicOpen s ≤ U₀ := C.basicOpen_le s
  obtain ⟨b, hbJ, hbgerm⟩ :=
    J.exists_mem_germ_ne_zero_of_le hWV (x := u.base w) hxs f₀ hf₀ hgermV
  -- ### Step 3: refine to an ideal element over the chart `U₀` itself (span induction)
  have hbmem : b ∈ (J.ideal U₀).map (C.presheaf.map (homOfLE hWU₀).op).hom :=
    (J.map_ideal hWU₀).symm ▸ hbJ
  have key : ∃ a ∈ J.ideal U₀, C.presheaf.germ U₀.1 (u.base w) hxU₀ a ≠ 0 := by
    by_contra hall
    push_neg at hall
    refine hbgerm ?_
    refine Submodule.span_induction
      (p := fun z _ => C.presheaf.germ (C.basicOpen s) (u.base w) hxs z = 0)
      ?_ ?_ ?_ ?_ hbmem
    · rintro z ⟨a, haJ, rfl⟩
      exact (C.presheaf.germ_res_apply
        (homOfLE (show C.basicOpen s ≤ U₀.1 from hWU₀)) (u.base w) hxs a).trans
        (hall a haJ)
    · exact map_zero _
    · intro y z _ _ hy hz
      rw [map_add, hy, hz, add_zero]
    · intro c z _ hz
      rw [smul_eq_mul, map_mul, hz, mul_zero]
  obtain ⟨a, haJ, hagerm⟩ := key
  -- ### Step 4: assemble
  rw [Scheme.Hom.finrank_eq_rankAtStalk_chart]
  have hle : (⊤ : (Spec (C.affineOpenCover.X (C.affineOpenCover.idx x))).Opens)
      ≤ u ⁻¹ᵁ U₀.1 := fun p _ => ⟨p, rfl⟩
  letI : Algebra ↑Γ(Spec (C.affineOpenCover.X (C.affineOpenCover.idx x)), ⊤)
      ↑Γ(Limits.pullback f u, ⊤) :=
    ((Limits.pullback.snd f u).appTop).hom.toAlgebra
  show Module.rankAtStalk (↑Γ(Limits.pullback f u, ⊤)) _ = 0
  refine Module.rankAtStalk_eq_zero_of_forall_smul_eq_zero _ (u.appLE U₀.1 ⊤ hle a)
    (fun m => ?_) ?_
  · -- the killing
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra,
      J.appTop_pullback_snd_appLE_eq_zero f g hf u U₀ hle a haJ, zero_mul]
  · -- the nonvanishing, through the stalk at `w`
    intro h0
    haveI : (((Spec (C.affineOpenCover.X (C.affineOpenCover.idx x))).isoSpec.hom
        w).asIdeal).IsPrime :=
      ((Spec (C.affineOpenCover.X (C.affineOpenCover.idx x))).isoSpec.hom w).isPrime
    obtain ⟨cc, hcc⟩ := (IsLocalization.map_eq_zero_iff
      (((Spec (C.affineOpenCover.X (C.affineOpenCover.idx x))).isoSpec.hom
        w).asIdeal.primeCompl)
      (Localization.AtPrime _) (u.appLE U₀.1 ⊤ hle a)).mp h0
    -- the definition's prime is `primeIdealOf` of `w` over the top of the chart
    have hq : ((Spec (C.affineOpenCover.X (C.affineOpenCover.idx x))).isoSpec.hom w)
        = ((isAffineOpen_top (Spec (C.affineOpenCover.X
            (C.affineOpenCover.idx x)))).primeIdealOf ⟨w, TopologicalSpace.Opens.mem_top w⟩) := by
      rw [IsAffineOpen.primeIdealOf_eq_map_closedPoint]
      rfl
    -- the germ of the pulled element at `w` is nonzero (stalk map of an open immersion)
    have hgermA : (Spec (C.affineOpenCover.X
        (C.affineOpenCover.idx x))).presheaf.germ ⊤ w (TopologicalSpace.Opens.mem_top w)
        (u.appLE U₀.1 ⊤ hle a) ≠ 0 := by
      rw [show (u.appLE U₀.1 ⊤ hle a)
          = ((Spec (C.affineOpenCover.X (C.affineOpenCover.idx
              x))).presheaf.map (homOfLE hle).op) ((u.app U₀.1) a) from rfl]
      rw [TopCat.Presheaf.germ_res_apply]
      rw [show ((Spec (C.affineOpenCover.X (C.affineOpenCover.idx
            x))).presheaf.germ (u ⁻¹ᵁ U₀.1) w ((homOfLE hle).le (TopologicalSpace.Opens.mem_top w)))
            ((u.app U₀.1) a)
          = (u.stalkMap w) (C.presheaf.germ U₀.1 (u.base w) hxU₀ a) from
        (Scheme.Hom.germ_stalkMap_apply u U₀.1 w hxU₀ a).symm]
      intro hzz
      have hinj : Function.Injective (u.stalkMap w).hom :=
        (ConcreteCategory.bijective_of_isIso (u.stalkMap w)).injective
      exact hagerm (hinj (by rw [show (u.stalkMap w).hom
        (C.presheaf.germ U₀.1 (u.base w) hxU₀ a)
          = (u.stalkMap w) (C.presheaf.germ U₀.1 (u.base w) hxU₀ a) from rfl, hzz, map_zero]))
    -- but the compl-element is a stalk unit, so the germ would vanish
    letI := (Spec (C.affineOpenCover.X (C.affineOpenCover.idx
      x))).presheaf.algebra_section_stalk (U := ⊤) ⟨w, TopologicalSpace.Opens.mem_top w⟩
    haveI := (isAffineOpen_top (Spec (C.affineOpenCover.X
      (C.affineOpenCover.idx x)))).isLocalization_stalk ⟨w, TopologicalSpace.Opens.mem_top w⟩
    have hcu : IsUnit (algebraMap
        ↑Γ(Spec (C.affineOpenCover.X (C.affineOpenCover.idx x)), ⊤)
        ↑((Spec (C.affineOpenCover.X (C.affineOpenCover.idx x))).presheaf.stalk w)
        (cc : ↑Γ(Spec (C.affineOpenCover.X (C.affineOpenCover.idx x)), ⊤))) :=
      IsLocalization.map_units _
        (⟨cc.1, hq ▸ cc.2⟩ : ((isAffineOpen_top (Spec (C.affineOpenCover.X
          (C.affineOpenCover.idx x)))).primeIdealOf
            ⟨w, TopologicalSpace.Opens.mem_top w⟩).asIdeal.primeCompl)
    refine hgermA ?_
    have hmap := congrArg (algebraMap
      ↑Γ(Spec (C.affineOpenCover.X (C.affineOpenCover.idx x)), ⊤)
      ↑((Spec (C.affineOpenCover.X (C.affineOpenCover.idx x))).presheaf.stalk w)) hcc
    rw [map_mul, map_zero] at hmap
    have hz := (IsUnit.mul_right_eq_zero hcu).mp hmap
    exact hz

end AlgebraicGeometry
