/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.SchemeActionFree
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski

/-!
# The quotient of a relatively-affine scheme by a finite group action (relative Spec)

For a finite group `G` acting on `Z` over `f : Z ⟶ S` **affine** (`hover : σ.hom γ ≫ f = f`),
we construct the quotient `Z/G` **over an arbitrary base `S`** — no separatedness or
affine-diagonal hypothesis on `Z` or `S` — as the glued relative Spec of the invariants
presheaf `U ↦ Γ(Z, f⁻¹U)ᴳ` on the small affine Zariski site of `S`.

This is the construction Katz–Mazur cite for the KM 7.1.3 quotient step (p. 190):

> "By [De-Ga III, §2, 6.1], we know that if a finite group `G` operates freely and
> `S`-linearly on an affine `S`-scheme `X`, then the quotient `X/G` exists, `X` is a
> finite etale `G`-torsor over `X/G`, and the formation of `X/G` commutes with arbitrary
> base-change `S′ → S`."

(The bare existence of the quotient — projection, structure map, categorical universal
property — needs **no freeness**; freeness enters only the finite-étale-torsor and
base-change addenda, exactly as in KM 7.1.3(2)/(3c) vs 7.1.3(1).)

The gluing engine is mathlib's `AlgebraicGeometry.relativeGluingData`
(`Mathlib/AlgebraicGeometry/Sites/SmallAffineZariski.lean`, feeding
`Scheme.Cover.RelativeGluingData`, stacks 01LH), applied to the `Coequifibered`
structural map `𝒪_S ⟶ (U ↦ Γ(Z, f⁻¹U)ᴳ)`; the file is a line-by-line mirror of
`Mathlib/AlgebraicGeometry/Normalization.lean` (relative normalization, the same engine
applied to the integral-closure presheaf) with the invariants subalgebra in place of the
integral closure. The chart-level algebra ("localization of invariants = invariants of
the localization", the categorical quotient property of `Spec Aᴳ`, the free-action
finite/étale/torsor facts) is already proven in `ForMathlib/InvariantLocalization.lean`,
`ForMathlib/AffineQuotient.lean`, `ForMathlib/EtaleCancellation.lean` and
`ForMathlib/SchemeActionFree.lean`; this file only assembles it over the site.

This supersedes the affine-diagonal-gated glued quotient of
`ForMathlib/SchemeQuotient.lean` (T-Q5) as the foundation for the Γ_H quotient-problem
data: the three consumers in `Moduli/GammaHRepresentability.lean`
(`exists_quotient_of_isAffineHom`, `quotientπ_finite_etale_surjective`,
`exists_quotient_baseChange_of_free`) keep their conclusion shapes and lose the
`IsAffineHom (pullback.diagonal (terminal.from Z))` instance, which was FALSE for
general `Ell/R` bases (a constant curve over a plane with doubled origin).
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry

namespace SchemeAction

variable {G : Type*} [Group G] [Finite G] {Z S : Scheme.{u}}
variable (σ : SchemeAction G Z) (f : Z ⟶ S)
variable (hover : ∀ γ : G, σ.hom γ ≫ f = f)

/-! ### The invariants diagram on the small affine Zariski site of the base -/

include hover in
/-- The `f`-preimage of any open of the base is stable under an action over `f`
(immediate from `hover`; the atlas-stability observation of [GHB3], now a lemma). -/
theorem isStableOpen_preimage (U : S.Opens) : σ.IsStableOpen (f ⁻¹ᵁ U) := by
  intro g
  show (σ.hom g ≫ f) ⁻¹ᵁ U = f ⁻¹ᵁ U
  rw [hover g]

/-- Restriction of sections along nested stable opens is `G`-equivariant: the section
action (`gammaMulSemiringAction`) commutes with the presheaf restriction map. -/
theorem gamma_map_smul {V U : Z.Opens} (hV : σ.IsStableOpen V) (hU : σ.IsStableOpen U)
    (hle : U ≤ V) (g : G) (s : Γ(Z, V)) :
    letI := σ.gammaMulSemiringAction hV
    letI := σ.gammaMulSemiringAction hU
    (Z.presheaf.map (homOfLE hle).op) (g • s) = g • (Z.presheaf.map (homOfLE hle).op) s := by
  letI := σ.gammaMulSemiringAction hV
  letI := σ.gammaMulSemiringAction hU
  show (Z.presheaf.map (homOfLE hle).op).hom
      (((σ.hom g).appLE V V (hV.le_preimage g)).hom s)
    = ((σ.hom g).appLE U U (hU.le_preimage g)).hom
      ((Z.presheaf.map (homOfLE hle).op).hom s)
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map,
    Scheme.Hom.map_appLE]

/-- The base change of a scheme action lying over `S` along `g : T ⟶ S`: the induced
action on `pullback f g` (trivial on the `T`-leg). Needed to *state* KM 7.1.3(3c).

HOIST of `Moduli/GammaHRepresentability.lean`'s `SchemeAction.basePullback` (verbatim;
that file's copy is deleted when it imports this file — its own section banner already
says "`/cleanup` may relocate this section to `ForMathlib/`"). -/
noncomputable def basePullback
    {G : Type*} [Group G] {Z S T : Scheme.{u}}
    (σ : SchemeAction G Z) (f : Z ⟶ S) (hover : ∀ γ : G, σ.hom γ ≫ f = f)
    (g : T ⟶ S) : SchemeAction G (pullback f g) where
  hom γ := pullback.map f g f g (σ.hom γ) (𝟙 T) (𝟙 S)
    (by rw [Category.comp_id, hover γ]) (by rw [Category.comp_id, Category.id_comp])
  hom_one := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, σ.hom_one, Category.comp_id, Category.id_comp]
    · rw [pullback.lift_snd, Category.comp_id, Category.id_comp]
  hom_mul := fun a b => by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc,
        σ.hom_mul, Category.assoc]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, pullback.lift_snd_assoc,
        Category.comp_id, Category.comp_id]

/-- The invariants presheaf on the small affine Zariski site of `S`:
`U ↦ Γ(Z, f⁻¹U)ᴳ`. The relative-Spec substrate for the quotient `Z/G` over `S`
(mirror of `Scheme.Hom.normalizationDiagram` with the fixed-point subalgebra in place
of the integral closure). -/
def invariantsDiagram : S.AffineZariskiSiteᵒᵖ ⥤ CommRingCat where
  obj U :=
    letI := σ.gammaMulSemiringAction (σ.isStableOpen_preimage f hover U.unop.1)
    .of (FixedPoints.subalgebra ℤ ↑Γ(Z, f ⁻¹ᵁ U.unop.1) G)
  map {V U} i :=
    letI := σ.gammaMulSemiringAction (σ.isStableOpen_preimage f hover V.unop.1)
    letI := σ.gammaMulSemiringAction (σ.isStableOpen_preimage f hover U.unop.1)
    CommRingCat.ofHom <|
      ((Z.presheaf.map (homOfLE (f.preimage_mono
          (Scheme.AffineZariskiSite.toOpens_mono i.unop.le))).op).hom.comp
        (FixedPoints.subalgebra ℤ ↑Γ(Z, f ⁻¹ᵁ V.unop.1) G).val.toRingHom).invariantsCorestrict
        (R₀ := ℤ) (fun g r => by
          have h := σ.gamma_map_smul (σ.isStableOpen_preimage f hover V.unop.1)
            (σ.isStableOpen_preimage f hover U.unop.1)
            (f.preimage_mono (Scheme.AffineZariskiSite.toOpens_mono i.unop.le)) g
            (r : Γ(Z, f ⁻¹ᵁ V.unop.1))
          show g • (Z.presheaf.map (homOfLE (f.preimage_mono
              (Scheme.AffineZariskiSite.toOpens_mono i.unop.le))).op).hom
              (r : Γ(Z, f ⁻¹ᵁ V.unop.1))
            = (Z.presheaf.map (homOfLE (f.preimage_mono
              (Scheme.AffineZariskiSite.toOpens_mono i.unop.le))).op).hom
              (r : Γ(Z, f ⁻¹ᵁ V.unop.1))
          rw [← h, r.2 g])
  map_id := by
    intro U
    ext r
    change (Z.presheaf.map (𝟙 (Opposite.op (f ⁻¹ᵁ (U.unop.1 : S.Opens))))).hom
        (r : Γ(Z, f ⁻¹ᵁ (U.unop.1 : S.Opens)))
      = (r : Γ(Z, f ⁻¹ᵁ (U.unop.1 : S.Opens)))
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp := by
    intro U V W i j
    ext r
    change (Z.presheaf.map
        ((homOfLE (f.preimage_mono (Scheme.AffineZariskiSite.toOpens_mono i.unop.le))).op ≫
          (homOfLE (f.preimage_mono (Scheme.AffineZariskiSite.toOpens_mono j.unop.le))).op)).hom
        (r : Γ(Z, f ⁻¹ᵁ (U.unop.1 : S.Opens)))
      = (Z.presheaf.map
          (homOfLE (f.preimage_mono (Scheme.AffineZariskiSite.toOpens_mono j.unop.le))).op).hom
        ((Z.presheaf.map
          (homOfLE (f.preimage_mono (Scheme.AffineZariskiSite.toOpens_mono i.unop.le))).op).hom
          (r : Γ(Z, f ⁻¹ᵁ (U.unop.1 : S.Opens))))
    rw [CategoryTheory.Functor.map_comp]
    rfl

/-- The structural map `𝒪_S ⟶ (U ↦ Γ(Z, f⁻¹U)ᴳ)`: per chart it is the descended
chart ring map `quotientDescRing` (the corestriction of `f.appLE` to the invariants,
[GHB3]-layer). Mirror of `normalizationDiagramMap`. -/
def invariantsDiagramMap :
    (Scheme.AffineZariskiSite.toOpensFunctor S).op ⋙ S.presheaf ⟶
      σ.invariantsDiagram f hover where
  app U := CommRingCat.ofHom
    (σ.quotientDescRing f hover U.unop.1 (σ.isStableOpen_preimage f hover U.unop.1))
  naturality := by
    intro U V i
    letI := σ.gammaMulSemiringAction (σ.isStableOpen_preimage f hover (U.unop.1 : S.Opens))
    letI := σ.gammaMulSemiringAction (σ.isStableOpen_preimage f hover (V.unop.1 : S.Opens))
    ext r
    refine Subtype.ext ?_
    have hdiag : (σ.invariantsDiagram f hover).map i ≫
          CommRingCat.ofHom (algebraMap
            (FixedPoints.subalgebra ℤ ↑Γ(Z, f ⁻¹ᵁ (V.unop.1 : S.Opens)) G)
            ↑Γ(Z, f ⁻¹ᵁ (V.unop.1 : S.Opens)))
        = CommRingCat.ofHom (algebraMap
            (FixedPoints.subalgebra ℤ ↑Γ(Z, f ⁻¹ᵁ (U.unop.1 : S.Opens)) G)
            ↑Γ(Z, f ⁻¹ᵁ (U.unop.1 : S.Opens))) ≫
          Z.presheaf.map (homOfLE (f.preimage_mono
            (Scheme.AffineZariskiSite.toOpens_mono i.unop.le))).op := by
      ext x
      rfl
    have hcollV := σ.ofHom_quotientDescRing_algebraMap f hover (V.unop.1 : S.Opens)
      (σ.isStableOpen_preimage f hover (V.unop.1 : S.Opens))
    have hcollU := σ.ofHom_quotientDescRing_algebraMap f hover (U.unop.1 : S.Opens)
      (σ.isStableOpen_preimage f hover (U.unop.1 : S.Opens))
    have hkey : (((Scheme.AffineZariskiSite.toOpensFunctor S).op ⋙ S.presheaf).map i ≫
          CommRingCat.ofHom (σ.quotientDescRing f hover (V.unop.1 : S.Opens)
            (σ.isStableOpen_preimage f hover (V.unop.1 : S.Opens)))) ≫
          CommRingCat.ofHom (algebraMap
            (FixedPoints.subalgebra ℤ ↑Γ(Z, f ⁻¹ᵁ (V.unop.1 : S.Opens)) G)
            ↑Γ(Z, f ⁻¹ᵁ (V.unop.1 : S.Opens)))
        = (CommRingCat.ofHom (σ.quotientDescRing f hover (U.unop.1 : S.Opens)
            (σ.isStableOpen_preimage f hover (U.unop.1 : S.Opens))) ≫
          (σ.invariantsDiagram f hover).map i) ≫
          CommRingCat.ofHom (algebraMap
            (FixedPoints.subalgebra ℤ ↑Γ(Z, f ⁻¹ᵁ (V.unop.1 : S.Opens)) G)
            ↑Γ(Z, f ⁻¹ᵁ (V.unop.1 : S.Opens))) := by
      refine ((Category.assoc _ _ _).trans ?_).trans (Category.assoc _ _ _).symm
      refine (congrArg (fun φ =>
        (((Scheme.AffineZariskiSite.toOpensFunctor S).op ⋙ S.presheaf).map i) ≫ φ)
        hcollV).trans ?_
      refine Eq.trans ?_ (congrArg (fun φ =>
        CommRingCat.ofHom (σ.quotientDescRing f hover (U.unop.1 : S.Opens)
          (σ.isStableOpen_preimage f hover (U.unop.1 : S.Opens))) ≫ φ) hdiag.symm)
      have hmid : (((Scheme.AffineZariskiSite.toOpensFunctor S).op ⋙ S.presheaf).map i ≫
            f.appLE (V.unop.1 : S.Opens) (f ⁻¹ᵁ (V.unop.1 : S.Opens)) le_rfl)
          = f.appLE (U.unop.1 : S.Opens) (f ⁻¹ᵁ (U.unop.1 : S.Opens)) le_rfl ≫
            Z.presheaf.map (homOfLE (f.preimage_mono
              (Scheme.AffineZariskiSite.toOpens_mono i.unop.le))).op :=
        (Scheme.Hom.map_appLE f le_rfl
          ((Scheme.AffineZariskiSite.toOpensFunctor S).op.map i)).trans
          (Scheme.Hom.appLE_map f le_rfl (homOfLE (f.preimage_mono
            (Scheme.AffineZariskiSite.toOpens_mono i.unop.le))).op).symm
      refine hmid.trans ?_
      rw [← Category.assoc, hcollU]
    exact congr($(hkey) r)

/-- **Localization of invariants = invariants of the localization** (abstract form, the
KM A7.1 flat case for a finite group): if `ρ : A →+* A'` is an equivariant
`Away s`-localization at an invariant `s`, then the corestriction
`Aᴳ →+* A'ᴳ` is an `Away ⟨s⟩`-localization. No freeness, no invertibility of `|G|` —
only finiteness (to clear denominators uniformly over the group). -/
theorem _root_.AlgebraicGeometry.isLocalization_away_fixedPoints
    {G₀ : Type*} [Group G₀] [Finite G₀]
    {A A' : Type*} [CommRing A] [CommRing A']
    [MulSemiringAction G₀ A] [MulSemiringAction G₀ A']
    (ρ : A →+* A') (hρ : ∀ (g : G₀) (a : A), ρ (g • a) = g • ρ a)
    (s : A) (hs : ∀ g : G₀, g • s = s)
    [Algebra A A'] (halg : algebraMap A A' = ρ) [IsLocalization.Away s A']
    (ρG : FixedPoints.subalgebra ℤ A G₀ →+* FixedPoints.subalgebra ℤ A' G₀)
    (hρG : ∀ x : FixedPoints.subalgebra ℤ A G₀, (ρG x : A') = ρ (x : A)) :
    letI : Algebra (FixedPoints.subalgebra ℤ A G₀) (FixedPoints.subalgebra ℤ A' G₀) :=
      ρG.toAlgebra
    IsLocalization.Away (⟨s, hs⟩ : FixedPoints.subalgebra ℤ A G₀)
      (FixedPoints.subalgebra ℤ A' G₀) := by
  letI : Algebra (FixedPoints.subalgebra ℤ A G₀) (FixedPoints.subalgebra ℤ A' G₀) :=
    ρG.toAlgebra
  classical
  haveI := Fintype.ofFinite G₀
  have halgG : ∀ x : FixedPoints.subalgebra ℤ A G₀,
      (algebraMap (FixedPoints.subalgebra ℤ A G₀) (FixedPoints.subalgebra ℤ A' G₀) x : A')
        = ρ (x : A) := fun x => hρG x
  have hρs : ∀ g : G₀, g • ρ s = ρ s := fun g => by rw [← hρ, hs]
  refine ⟨?_, ?_, ?_⟩
  · -- map_units
    rintro ⟨y, n, rfl⟩
    have hu' : IsUnit ((ρ s) ^ n) := by
      have h := IsLocalization.Away.algebraMap_pow_isUnit (S := A') (x := s) n
      rwa [halg] at h
    obtain ⟨u, hu⟩ := hu'
    have hUinv : ∀ g : G₀, g • (↑u : A') = ↑u := fun g => by
      rw [hu, smul_pow', hρs]
    have hInvinv : ∀ g : G₀, g • (↑u⁻¹ : A') = ↑u⁻¹ := by
      intro g
      have h1 : (g • (↑u⁻¹ : A')) * ↑u = 1 := by
        conv_lhs => rw [← hUinv g]
        rw [← smul_mul', u.inv_mul, smul_one]
      calc g • (↑u⁻¹ : A') = (g • (↑u⁻¹ : A')) * (↑u * ↑u⁻¹) := by
            rw [u.mul_inv, mul_one]
        _ = ((g • (↑u⁻¹ : A')) * ↑u) * ↑u⁻¹ := (mul_assoc _ _ _).symm
        _ = ↑u⁻¹ := by rw [h1, one_mul]
    refine IsUnit.of_mul_eq_one
      (⟨(↑u⁻¹ : A'), fun g => hInvinv g⟩ : FixedPoints.subalgebra ℤ A' G₀) ?_
    refine Subtype.ext ?_
    show (algebraMap (FixedPoints.subalgebra ℤ A G₀) (FixedPoints.subalgebra ℤ A' G₀)
        ((⟨s, hs⟩ : FixedPoints.subalgebra ℤ A G₀) ^ n) : A') * ↑u⁻¹ = 1
    rw [halgG, show (((⟨s, hs⟩ : FixedPoints.subalgebra ℤ A G₀) ^ n : _) : A) = s ^ n from
      SubmonoidClass.coe_pow _ _, map_pow, ← hu, u.mul_inv]
  · -- surj
    rintro ⟨z, hz⟩
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (S := A') (x := s) z
    rw [halg] at ha
    have heq : ∀ g : G₀, ρ (g • a) = ρ a := by
      intro g
      rw [hρ, ← ha, smul_mul', hz g, smul_pow', hρs]
    have hker : ∀ g : G₀, ∃ m : ℕ, s ^ m * (g • a) = s ^ m * a := by
      intro g
      obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers s) A').mp
        (by simpa [halg] using heq g)
      obtain ⟨m, hm⟩ := c.2
      rw [← hm] at hc
      exact ⟨m, hc⟩
    choose m hm using hker
    set M := Finset.univ.sup m with hM
    have hMs : ∀ g : G₀, s ^ M * (g • a) = s ^ M * a := by
      intro g
      have hle : m g ≤ M := Finset.le_sup (Finset.mem_univ g)
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      calc s ^ M * (g • a) = s ^ d * (s ^ m g * (g • a)) := by rw [hd, pow_add]; ring
        _ = s ^ d * (s ^ m g * a) := by rw [hm g]
        _ = s ^ M * a := by rw [hd, pow_add]; ring
    have hbInv : ∀ g : G₀, g • (s ^ M * a) = s ^ M * a := by
      intro g
      have h1 : g • (s ^ M * a) = s ^ M * (g • a) := by
        rw [smul_mul', smul_pow', hs]
      rw [h1, hMs g]
    refine ⟨⟨⟨s ^ M * a, hbInv⟩,
      ⟨(⟨s, hs⟩ : FixedPoints.subalgebra ℤ A G₀) ^ (n + M), ⟨n + M, rfl⟩⟩⟩, ?_⟩
    refine Subtype.ext ?_
    show z * (algebraMap (FixedPoints.subalgebra ℤ A G₀) (FixedPoints.subalgebra ℤ A' G₀)
        ((⟨s, hs⟩ : FixedPoints.subalgebra ℤ A G₀) ^ (n + M)) : A')
      = (algebraMap (FixedPoints.subalgebra ℤ A G₀) (FixedPoints.subalgebra ℤ A' G₀)
        (⟨s ^ M * a, hbInv⟩ : FixedPoints.subalgebra ℤ A G₀) : A')
    rw [halgG, halgG, show (((⟨s, hs⟩ : FixedPoints.subalgebra ℤ A G₀) ^ (n + M) : _) : A)
        = s ^ (n + M) from SubmonoidClass.coe_pow _ _]
    show z * ρ (s ^ (n + M)) = ρ (s ^ M * a)
    rw [map_pow, map_mul, map_pow, pow_add]
    linear_combination (ρ s) ^ M * ha
  · -- exists_of_eq
    intro x y hxy
    have hval : ρ (x : A) = ρ (y : A) := by
      have h := congrArg Subtype.val hxy
      rwa [halgG, halgG] at h
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers s) A').mp
      (by simpa [halg] using hval)
    obtain ⟨k, hk⟩ := c.2
    rw [← hk] at hc
    refine ⟨⟨(⟨s, hs⟩ : FixedPoints.subalgebra ℤ A G₀) ^ k, ⟨k, rfl⟩⟩, ?_⟩
    refine Subtype.ext ?_
    show (((⟨s, hs⟩ : FixedPoints.subalgebra ℤ A G₀) ^ k : _) : A) * (x : A)
      = (((⟨s, hs⟩ : FixedPoints.subalgebra ℤ A G₀) ^ k : _) : A) * (y : A)
    rw [show (((⟨s, hs⟩ : FixedPoints.subalgebra ℤ A G₀) ^ k : _) : A) = s ^ k from
      SubmonoidClass.coe_pow _ _]
    exact hc

/-- Scheme-side chart localization for an affine morphism: over an affine open `U₀` of
the base, the preimage of `D_{U₀}(r)` is the basic open of the `appLE`-image, and its
sections are the away-localization. -/
theorem _root_.AlgebraicGeometry.isLocalization_away_preimage_basicOpen
    {Z S : Scheme.{u}} (f : Z ⟶ S) [IsAffineHom f] {U₀ : S.Opens}
    (hU : IsAffineOpen U₀) (r : Γ(S, U₀)) :
    letI : Algebra Γ(Z, f ⁻¹ᵁ U₀) Γ(Z, f ⁻¹ᵁ S.basicOpen r) :=
      ((Z.presheaf.map (homOfLE (f.preimage_mono (S.basicOpen_le r))).op).hom).toAlgebra
    IsLocalization.Away ((f.appLE U₀ (f ⁻¹ᵁ U₀) le_rfl).hom r)
      Γ(Z, f ⁻¹ᵁ S.basicOpen r) := by
  letI : Algebra Γ(Z, f ⁻¹ᵁ U₀) Γ(Z, f ⁻¹ᵁ S.basicOpen r) :=
    ((Z.presheaf.map (homOfLE (f.preimage_mono (S.basicOpen_le r))).op).hom).toAlgebra
  haveI hUZ : IsAffineOpen (f ⁻¹ᵁ U₀) := hU.preimage f
  have hopens : f ⁻¹ᵁ S.basicOpen r
      = Z.basicOpen ((f.appLE U₀ (f ⁻¹ᵁ U₀) le_rfl).hom r) := by
    rw [Scheme.basicOpen_appLE]
    exact (inf_eq_right.mpr (f.preimage_mono (S.basicOpen_le r))).symm
  exact hUZ.isLocalization_of_eq_basicOpen _
    (homOfLE (f.preimage_mono (S.basicOpen_le r))) hopens

variable [IsAffineHom f]

/-- **Invariants form a quasi-coherent `𝒪_S`-algebra**: the structural map is
`Coequifibered`, i.e. `Γ(Z, f⁻¹(D_U(r)))ᴳ` is the away-localization of
`Γ(Z, f⁻¹U)ᴳ` at the (invariant) image of `r`. Chart-level content: `f` affine
identifies `Γ(Z, f⁻¹(D_U(r)))` with the localization of `Γ(Z, f⁻¹U)` at `f♯r`, and
"localization of invariants = invariants of the localization" for a finite group
(`ForMathlib/InvariantLocalization.lean`: `mem_range_fixedPoints_awayMap_iff`,
`fixedPoints_awayMap_injective`). KM's appendix A7.1 ambient fact; mirror of
`coequifibered_normalizationDiagramMap`. -/
theorem coequifibered_invariantsDiagramMap :
    (σ.invariantsDiagramMap f hover).Coequifibered := by
  refine Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway.mpr
    fun U r => ?_
  letI := σ.gammaMulSemiringAction (σ.isStableOpen_preimage f hover U.1)
  letI := σ.gammaMulSemiringAction (σ.isStableOpen_preimage f hover (S.basicOpen r))
  letI : Algebra Γ(Z, f ⁻¹ᵁ (U.1 : S.Opens)) Γ(Z, f ⁻¹ᵁ S.basicOpen r) :=
    ((Z.presheaf.map (homOfLE (f.preimage_mono (S.basicOpen_le r))).op).hom).toAlgebra
  haveI hloc : IsLocalization.Away ((f.appLE (U.1 : S.Opens) (f ⁻¹ᵁ (U.1 : S.Opens))
      le_rfl).hom r) Γ(Z, f ⁻¹ᵁ S.basicOpen r) :=
    AlgebraicGeometry.isLocalization_away_preimage_basicOpen f U.2 r
  exact AlgebraicGeometry.isLocalization_away_fixedPoints
    (G₀ := G)
    (ρ := (Z.presheaf.map (homOfLE (f.preimage_mono (S.basicOpen_le r))).op).hom)
    (fun g a => σ.gamma_map_smul (σ.isStableOpen_preimage f hover U.1)
      (σ.isStableOpen_preimage f hover (S.basicOpen r))
      (f.preimage_mono (S.basicOpen_le r)) g a)
    ((f.appLE (U.1 : S.Opens) (f ⁻¹ᵁ (U.1 : S.Opens)) le_rfl).hom r)
    (fun g => σ.gamma_appLE_invariant f hover
      (σ.isStableOpen_preimage f hover U.1) le_rfl g r)
    rfl
    (((σ.invariantsDiagram f hover).map
      (homOfLE (Scheme.AffineZariskiSite.basicOpen_le U r)).op).hom)
    (fun x => rfl)

/-! ### The quotient scheme, projection, and structure morphism -/

/-- The relative gluing datum of the invariants algebra (mirror of
`normalizationGlueData`). -/
def invariantsGlueData :=
  Scheme.AffineZariskiSite.relativeGluingData (σ.coequifibered_invariantsDiagramMap f hover)

/-- **The quotient of a relatively-affine scheme by a finite group action** over an
arbitrary base: the glued relative Spec of `U ↦ Γ(Z, f⁻¹U)ᴳ`. KM p. 190 / [De-Ga III
§2, 6.1] / SGA 3 V §4. NO hypotheses on `S` or on the diagonal of `Z`. -/
def relQuotient : Scheme.{u} :=
  (σ.invariantsGlueData f hover).glued

/-- The structure morphism `Z/G ⟶ S` (chartwise `Spec Γ(Z, f⁻¹U)ᴳ ⟶ U`). -/
def relQuotientStruct : σ.relQuotient f hover ⟶ S :=
  (σ.invariantsGlueData f hover).toBase

instance : ((σ.invariantsGlueData f hover).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- The chart component of the quotient projection (an atomic definition so the gluing
lemma unifies cheaply — the zero-kabstract barrier idiom). -/
def relQuotientπChart (U : S.AffineZariskiSite) :
    ((Scheme.AffineZariskiSite.directedCover S).pullback₁ f).X U ⟶
      σ.relQuotient f hover :=
  letI := σ.gammaMulSemiringAction (σ.isStableOpen_preimage f hover U.1)
  (pullbackRestrictIsoRestrict f _).hom ≫ (f ⁻¹ᵁ U.1).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom
      (FixedPoints.subalgebra ℤ ↑Γ(Z, f ⁻¹ᵁ U.1) G).val.toRingHom) ≫
    (σ.invariantsGlueData f hover).cover.f U

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Compatibility of the chart maps with the transition maps of the pullback cover
(the gluing obligation, named so the glue and its defining lemma elaborate
syntactically). -/
theorem relQuotientπ_compat {U V : S.AffineZariskiSite} (i : U ⟶ V) :
    Scheme.Cover.trans ((Scheme.AffineZariskiSite.directedCover S).pullback₁ f) i ≫
      σ.relQuotientπChart f hover V = σ.relQuotientπChart f hover U := by
  delta relQuotientπChart
  have hres : (pullbackRestrictIsoRestrict f U.1).inv ≫
      Scheme.Cover.trans ((Scheme.AffineZariskiSite.directedCover S).pullback₁ f) i ≫
      (pullbackRestrictIsoRestrict f V.1).hom = Z.homOfLE
        (f.preimage_mono (Scheme.AffineZariskiSite.toOpens_mono i.1.1)) := by
    rw [← cancel_mono (Scheme.Opens.ι _)]
    simp +instances [Scheme.Cover.trans, Scheme.Cover.locallyDirectedPullbackCover]
  rw [← Iso.inv_comp_eq, reassoc_of% hres,
    ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, ← Spec.map_comp_assoc]
  show _ ≫ Spec.map _ ≫ (σ.invariantsGlueData f hover).cover.f V = _
  simp only [Scheme.Cover.RelativeGluingData.cover_f]
  rw [← colimit.w (σ.invariantsGlueData f hover).functor i]
  dsimp [invariantsGlueData, Scheme.AffineZariskiSite.relativeGluingData]
  rw [← Spec.map_comp_assoc]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The quotient projection `Z ⟶ Z/G`, glued over the directed affine cover of `S`
from the chartwise `Spec Γ(Z, f⁻¹U) ⟶ Spec Γ(Z, f⁻¹U)ᴳ` (mirror of
`toNormalization`). -/
def relQuotientπ : Z ⟶ σ.relQuotient f hover :=
  Scheme.OpenCover.glueMorphismsOfLocallyDirected
    ((Scheme.AffineZariskiSite.directedCover S).pullback₁ f)
    (fun U => σ.relQuotientπChart f hover U)
    (fun {U V} i => σ.relQuotientπ_compat f hover i)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The pullback-cover component of the projection is the chart map (atomic gluing
lemma; `g` passed syntactically so unification is cheap). -/
theorem pullbackCover_f_comp_relQuotientπ (U : S.AffineZariskiSite) :
    ((Scheme.AffineZariskiSite.directedCover S).pullback₁ f).f U ≫
      σ.relQuotientπ f hover = σ.relQuotientπChart f hover U := by
  delta relQuotientπ
  exact Scheme.OpenCover.map_glueMorphismsOfLocallyDirected
    ((Scheme.AffineZariskiSite.directedCover S).pullback₁ f)
    (fun U => σ.relQuotientπChart f hover U)
    (fun {U V} i => σ.relQuotientπ_compat f hover i) U

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Defining property of the quotient projection on each chart (mirror of
`ι_toNormalization`). -/
@[reassoc]
theorem ι_relQuotientπ (U : S.AffineZariskiSite) :
    letI := σ.gammaMulSemiringAction (σ.isStableOpen_preimage f hover U.1)
    (f ⁻¹ᵁ (U.1 : S.Opens)).ι ≫ σ.relQuotientπ f hover =
      (f ⁻¹ᵁ (U.1 : S.Opens)).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
        (FixedPoints.subalgebra ℤ ↑Γ(Z, f ⁻¹ᵁ (U.1 : S.Opens)) G).val.toRingHom) ≫
      (σ.invariantsGlueData f hover).cover.f U := by
  rw [← cancel_epi (pullbackRestrictIsoRestrict f U.1).hom, ← Category.assoc]
  trans ((Scheme.AffineZariskiSite.directedCover S).pullback₁ f).f U ≫
    σ.relQuotientπ f hover
  · congr 1
    simp
  rw [σ.pullbackCover_f_comp_relQuotientπ f hover U]
  rfl

/-- The structure map on each glued chart (mirror of `ι_fromNormalization`). -/
@[reassoc]
theorem ι_relQuotientStruct (U : S.AffineZariskiSite) :
    colimit.ι (σ.invariantsGlueData f hover).functor U ≫ σ.relQuotientStruct f hover =
      Spec.map ((σ.invariantsDiagramMap f hover).app (.op U)) ≫ U.2.fromSpec :=
  colimit.ι_desc _ _

set_option backward.isDefEq.respectTransparency false in
/-- The projection descends `f`: `π ≫ f₀ = f` (mirror of
`toNormalization_fromNormalization`). -/
@[reassoc]
theorem relQuotientπ_comp_relQuotientStruct :
    σ.relQuotientπ f hover ≫ σ.relQuotientStruct f hover = f := by
  refine Scheme.Cover.hom_ext (Z.openCoverOfIsOpenCover _
    (.comap (iSup_affineOpens_eq_top S) f.base.1)) _ _ fun U => ?_
  refine (σ.ι_relQuotientπ_assoc f hover _ _).trans ?_
  simp only [Scheme.Cover.RelativeGluingData.cover_f]
  rw [σ.ι_relQuotientStruct f hover, ← Spec.map_comp_assoc]
  change (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (f.appLE _ _ le_rfl) ≫ _ = (f ⁻¹ᵁ U.1).ι ≫ _
  simp [Scheme.Hom.appLE]

set_option backward.isDefEq.respectTransparency false in
/-- The projection coequalizes the action (chartwise: `γ` acts trivially on
invariants, so `Spec (γ♯)` cancels against the invariants inclusion). -/
theorem hom_comp_relQuotientπ (γ : G) :
    σ.hom γ ≫ σ.relQuotientπ f hover = σ.relQuotientπ f hover := by
  refine Scheme.Cover.hom_ext (Z.openCoverOfIsOpenCover _
    (.comap (iSup_affineOpens_eq_top S) f.base.1)) _ _ fun U => ?_
  letI := σ.gammaMulSemiringAction (σ.isStableOpen_preimage f hover U.1)
  have hst := σ.isStableOpen_preimage f hover U.1
  show (f ⁻¹ᵁ (U.1 : S.Opens)).ι ≫ σ.hom γ ≫ σ.relQuotientπ f hover
    = (f ⁻¹ᵁ (U.1 : S.Opens)).ι ≫ σ.relQuotientπ f hover
  have hres : (f ⁻¹ᵁ (U.1 : S.Opens)).ι ≫ σ.hom γ
      = (σ.hom γ).resLE (f ⁻¹ᵁ (U.1 : S.Opens)) (f ⁻¹ᵁ (U.1 : S.Opens))
        (hst.le_preimage γ) ≫ (f ⁻¹ᵁ (U.1 : S.Opens)).ι :=
    (Scheme.Hom.resLE_comp_ι (e := hst.le_preimage γ)).symm
  rw [← Category.assoc, hres, Category.assoc, σ.ι_relQuotientπ f hover U,
    ← Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc (σ.hom γ) (f ⁻¹ᵁ (U.1 : S.Opens))
      (f ⁻¹ᵁ (U.1 : S.Opens)) (hst.le_preimage γ), ← Spec.map_comp_assoc]
  have hcol : CommRingCat.ofHom
        (FixedPoints.subalgebra ℤ ↑Γ(Z, f ⁻¹ᵁ (U.1 : S.Opens)) G).val.toRingHom ≫
        (σ.hom γ).appLE (f ⁻¹ᵁ (U.1 : S.Opens)) (f ⁻¹ᵁ (U.1 : S.Opens))
          (hst.le_preimage γ)
      = CommRingCat.ofHom
        (FixedPoints.subalgebra ℤ ↑Γ(Z, f ⁻¹ᵁ (U.1 : S.Opens)) G).val.toRingHom := by
    ext r
    exact r.2 γ
  rw [hcol]

/-- **The chart bridge**: over each affine chart `U` of the base, the quotient
projection restricts to the affine invariants projection
`Spec Γ(Z, f⁻¹U) ⟶ Spec Γ(Z, f⁻¹U)ᴳ` — the square

`(f⁻¹U) → Spec Γ(Z, f⁻¹U)ᴳ`, `(f⁻¹U) ↪ Z`, `Spec Γ(Z, f⁻¹U)ᴳ → Z/G`, `Z ⟶ Z/G`

is a pullback. This is the transfer principle that lets every chart-local fact of
`ForMathlib/AffineQuotient.lean` / `ForMathlib/SchemeActionFree.lean` (finite, étale,
surjective, torsor, base-change) be read off on `relQuotientπ`; composition of
`isPullback_natTrans_ι_toBase` with the `glueMorphismsOfLocallyDirected` chart
triangle of `relQuotientπ`. -/
theorem isPullback_relQuotientπ_chart (U : S.AffineZariskiSite) :
    letI := σ.gammaMulSemiringAction (σ.isStableOpen_preimage f hover U.1)
    IsPullback
      ((f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
        (FixedPoints.subalgebra ℤ ↑Γ(Z, f ⁻¹ᵁ U.1) G).val.toRingHom))
      (f ⁻¹ᵁ U.1).ι
      ((σ.invariantsGlueData f hover).cover.f U)
      (σ.relQuotientπ f hover) := by
  sorry

/-- The structure morphism of the quotient is affine (chartwise it is
`Spec Γ(Z, f⁻¹U)ᴳ ⟶ U`; affineness is Zariski-local on the target along the
directed cover, via `toBase_preimage_eq_opensRange_ι`). -/
instance isAffineHom_relQuotientStruct : IsAffineHom (σ.relQuotientStruct f hover) := by
  sorry

/-- The projection is integral (chartwise `Aᴳ → A` is integral: every `a` is a root of
`∏_g (T − g•a)`, KM 7.1.3(4) print p. 193; mathlib `Algebra.IsInvariant.isIntegral`). -/
instance isIntegralHom_relQuotientπ : IsIntegralHom (σ.relQuotientπ f hover) := by
  sorry

/-- **The categorical quotient property** (vs an ARBITRARY target scheme): an invariant
morphism `F : Z ⟶ Y` factors uniquely through the projection. Chart-level content is
`existsUnique_invariantsπ_lift` (`ForMathlib/AffineQuotient.lean`); glued over the
directed cover. Conclusion shape = the universal-property clause of the [GHB3]
`exists_quotient_of_isAffineHom` package. -/
theorem existsUnique_relQuotientπ_lift {Y : Scheme.{u}} (F : Z ⟶ Y)
    (hF : ∀ γ : G, σ.hom γ ≫ F = F) :
    ∃! q : σ.relQuotient f hover ⟶ Y, σ.relQuotientπ f hover ≫ q = F := by
  sorry

/-- **[GHB3′] (KM 7.1.3(1)/(3) existence, diagonal-free)** — the full package of the
former `exists_quotient_of_isAffineHom`, with the `IsAffineHom (pullback.diagonal
(terminal.from Z))` instance DELETED: for any affine invariant `f : Z ⟶ S` the
quotient exists with projection, structure map, invariance, and the categorical
universal property. This is the theorem that replaces the [GHB3] body and deletes
`hbase` from `nonempty_quotPkg` → `exists_quotientProblemData` →
`gammaH_relativelyRepresentable`. -/
theorem exists_quotient_of_isAffineHom_rel :
    ∃ (Z₀ : Scheme.{u}) (π : Z ⟶ Z₀) (f₀ : Z₀ ⟶ S), π ≫ f₀ = f ∧
      (∀ γ : G, σ.hom γ ≫ π = π) ∧
      ∀ {Y : Scheme.{u}} (F : Z ⟶ Y), (∀ γ : G, σ.hom γ ≫ F = F) →
        ∃! q : Z₀ ⟶ Y, π ≫ q = F := by
  sorry

/-! ### The free-action addenda: finite étale torsor, base change (KM 7.1.3(2),(3c)) -/

section Free

variable (hfree : ∀ {T : Scheme.{u}} (t : T ⟶ Z) (γ : G), γ ≠ 1 →
  t ≫ σ.hom γ = t → IsEmpty T)

/-- Free case: the projection is finite (chartwise `Aᴳ → A` is module-finite for a free
algebra action, `Module.Finite.of_isFreeAlgebraAction`; local on the target along the
chart cover). -/
theorem isFinite_relQuotientπ_of_free : IsFinite (σ.relQuotientπ f hover) := by
  sorry

/-- Free case: the projection is étale (chartwise `Algebra.Etale.of_isFreeAlgebraAction`). -/
theorem etale_relQuotientπ_of_free : Etale (σ.relQuotientπ f hover) := by
  sorry

/-- Free case: the projection is surjective (chartwise `Spec A ⟶ Spec Aᴳ` is surjective:
`Aᴳ → A` is integral and injective... chart core as in `quotientπ_surjective`). -/
theorem surjective_relQuotientπ_of_free : Surjective (σ.relQuotientπ f hover) := by
  sorry

/-- **[GHB5′] (KM 7.1.3(3c), diagonal-free)** — for a free action the quotient commutes
with arbitrary base change `g : T ⟶ S`: the base-changed projection
`pullback f g ⟶ pullback f₀ g` satisfies the quotient universal property for the
base-changed action. Conclusion tuple = the former `exists_quotient_baseChange_of_free`
minus the diagonal instance. Chart-level content: `[A711-BC]`
(`fixedPointsBaseChange_bijective_of_isFreeAlgebraAction`) via
`exists_invariantsπ_lift_baseChange_of_free` (`ForMathlib/AffineQuotient.lean`);
uniqueness via `epi_pullback_snd_invariantsπ_of_free`. -/
theorem exists_relQuotient_baseChange_of_free {T : Scheme.{u}} (g : T ⟶ S) :
    ∃ πT : pullback f g ⟶ pullback (σ.relQuotientStruct f hover) g,
      πT ≫ pullback.snd (σ.relQuotientStruct f hover) g = pullback.snd f g ∧
      πT ≫ pullback.fst (σ.relQuotientStruct f hover) g =
        pullback.fst f g ≫ σ.relQuotientπ f hover ∧
      (∀ γ : G, (σ.basePullback f hover g).hom γ ≫ πT = πT) ∧
      ∀ {Y : Scheme.{u}} (F : pullback f g ⟶ Y),
        (∀ γ : G, (σ.basePullback f hover g).hom γ ≫ F = F) →
          ∃! q : pullback (σ.relQuotientStruct f hover) g ⟶ Y, πT ≫ q = F := by
  sorry

end Free

end SchemeAction

end AlgebraicGeometry

end
