/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.GroupLaw
-- NOTE (P4, 2026-07-07): `import ModularCurves.EllipticCurve.PoleFiltration` deliberately
-- deferred to the T-W7.r-supply ticket (which will consume
-- `locallyWeierstrass_pushforward_O_eq_O`); nothing here references it yet, and keeping it
-- out decouples lane P4 builds from lane P3's in-flight file.
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import ModularCurves.ForMathlib.ConnectedTotalSpace
import ModularCurves.EllipticCurve.PoleFiltration

/-!
# The rigidity lemma and canonicity of the group law

**(T-W7 skeleton, lane P4 — `/develop --decompose` 2026-07-07.)** Mumford's rigidity lemma
(GIT Prop 6.1) transcribed from the source — cases 1 and 2 only (our curves carry the zero
section, so the sectionless fppf-descent case 3 is never needed) — together with the
corollary chain (GIT Cor 6.2 → 6.3 → 6.4 → 6.6) ending in the **canonicity of the group
law** over a locally noetherian base. The `H⁰`-hypothesis of GIT is replaced by universal
`O`-connectedness (`UniversallyOConnected`), which `PoleFiltration.lean` supplies for
locally-Weierstrass families by instantiation — no cohomology.

GIT's chapter convention is **locally noetherian** schemes and Prop 6.1 assumes **`S`
connected**; both are genuinely used (Artinian thickenings; Krull intersection; coherence;
clopen decomposition). The arbitrary-`S` upgrade is the separate spreading-out ticket
(T-W7.8), NOT this file.

Sources: Mumford GIT, Ch. 6 §1, pp. 115–117 — verbatim statement + proof quotes with
locators in `.mathlib-quality/tw7-source-quotes.md`; audit A4.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  MonObj
  MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

/-- **(T-W7.7a-hyp)** Universal `O`-connectedness of `p : X ⟶ S`: after every base change,
the structure map on sections is an isomorphism on every open — `O_T ≅ (p_T)_* O_{X_T}`
naturally. This replaces GIT 6.1's fibrewise `H⁰(X_s, O_{X_s}) = κ(s)` hypothesis; for
locally-Weierstrass families it holds by instantiating the uniform global-sections theorem
(`locallyWeierstrass_pushforward_O_eq_O`), with no cohomology. Source: GIT p. 115 ("One
checks that `p_*(o_X) ≅ o_S`", case 1) + audit A4/R1. -/
def UniversallyOConnected {X S : Scheme.{u}} (p : X ⟶ S) : Prop :=
  ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ S) (U : T.Opens), IsIso ((pullback.snd p g).app U)

set_option backward.isDefEq.respectTransparency.types false in
/-- **(T-W7.7a-hyp-supply, PROVEN)** Locally-Weierstrass families are universally
`O`-connected: base changes are again locally Weierstrass (`LocallyWeierstrass.baseChange`
and the base-change stability of the geometry fields), so the uniform global-sections
theorem `locallyWeierstrass_pushforward_O_eq_O` (T-W7.0i·i5) instantiates on the
base-changed geometry. -/
theorem EllipticCurveGeom.universallyOConnected {S : Scheme.{u}} (G : EllipticCurveGeom S) :
    UniversallyOConnected G.π := by
  intro T g U
  let G' : EllipticCurveGeom T :=
    { E := pullback G.π g
      π := pullback.snd G.π g
      zero := pullback.lift (g ≫ G.zero) (𝟙 T)
        (by rw [Category.assoc, G.zero_π, Category.comp_id, Category.id_comp])
      zero_π := pullback.lift_snd _ _ _
      smooth := by
        haveI : MorphismProperty.IsStableUnderBaseChange
            (@SmoothOfRelativeDimension 1) :=
          AlgebraicGeometry.smoothOfRelativeDimension_isStableUnderBaseChange 1
        exact MorphismProperty.pullback_snd _ _ G.smooth
      proper := MorphismProperty.pullback_snd _ _ G.proper
      localModel := G.localModel.baseChange g }
  exact locallyWeierstrass_pushforward_O_eq_O G' U

/-- Morphisms into an affine scheme are determined by their pullback on global sections
(the `Γ`–`Spec` adjunction, in the form every rigidity argument below consumes). -/
theorem hom_ext_of_isAffine {W Z : Scheme.{u}} [IsAffine Z] {f g : W ⟶ Z}
    (h : f.appTop = g.appTop) : f = g := by
  rw [← cancel_mono Z.isoSpec.hom, Scheme.isoSpec, asIso_hom,
    Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality, h]

set_option backward.isDefEq.respectTransparency.types false in
/-- **(T-W7.7a-R1, the affine core)** Every `S`-morphism from `X ×_S Y` to an affine scheme
factors uniquely through the projection to `Y`, when `p : X ⟶ S` is universally
`O`-connected: morphisms to an affine are ring maps out of global sections, and
`Γ(X ×_S Y) = Γ(Y)`. This is GIT case 1's ringed-space argument in its consumed form.
Source: GIT p. 115–116 (case 1: "`o_Y → f_*(o_X) ≅ η_*(p_*(o_X)) ≅ η_*(o_S)` … is precisely
the extra structure required"). -/
theorem exists_unique_factor_of_isAffine {X S : Scheme.{u}} {p : X ⟶ S}
    (hp : UniversallyOConnected p) {Y : Scheme.{u}} (g : Y ⟶ S)
    {Z : Scheme.{u}} [IsAffine Z] (f : pullback p g ⟶ Z) :
    ∃! h : Y ⟶ Z, f = pullback.snd p g ≫ h := by
  have hφ : IsIso ((pullback.snd p g).appTop) := hp g ⊤
  -- the transported ring map `Γ(Z) ⟶ Γ(Y)` and the corresponding morphism `Y ⟶ Z`
  set ψ := f.appTop ≫ inv ((pullback.snd p g).appTop) with hψ
  have hZinv : Z.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(Z, ⊤)).inv := by
    rw [← Iso.hom_comp_eq_id, ← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop,
      show Z.isoSpec.inv ≫ Z.toSpecΓ = 𝟙 _ from Z.isoSpec.inv_hom_id, Scheme.Hom.id_appTop]
  set h₀ : Y ⟶ Z := (ΓSpec.adjunction.homEquiv Y (Opposite.op Γ(Z, ⊤))) ψ.op ≫
    Z.isoSpec.inv with hh₀
  have happ : h₀.appTop = ψ := by
    rw [hh₀, Scheme.Hom.comp_appTop, hZinv, ΓSpec_adjunction_homEquiv_eq]
    exact Iso.inv_hom_id_assoc _ _
  have hfac : ∀ h : Y ⟶ Z, f = pullback.snd p g ≫ h ↔ h.appTop = ψ := by
    intro h
    constructor
    · intro hE
      have h2 : f.appTop = h.appTop ≫ (pullback.snd p g).appTop := by
        rw [hE, Scheme.Hom.comp_appTop]
      rw [hψ, h2]
      simp
    · intro hh
      refine (hom_ext_of_isAffine ?_).symm
      rw [Scheme.Hom.comp_appTop, hh, hψ, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact ⟨h₀, (hfac h₀).mpr happ, fun h' hh' =>
    hom_ext_of_isAffine (((hfac h').mp hh').trans happ.symm)⟩

/-- **(T-W7.7a-R1′ core, GIT case 1)** Rigidity for morphisms landing in one affine chart:
a morphism `f : X ⟶ Y` over `S` whose topological image is contained in the range of an
open immersion from an affine scheme, with `X` universally `O`-connected over `S` and
carrying a section, factors through the section `η := e ≫ f` of `Y ⟶ S`. The chart is a
parameter (rather than produced from a constant-image hypothesis) so that the seed step of
case 2 can feed it the affine `V ×_S Spec κ(s)` without any point-injectivity reasoning
about fibre products. Source: GIT p. 115, case 1 (verbatim in quotes file). -/
theorem rigidity_of_range_le_affine {X Y S : Scheme.{u}}
    {p : X ⟶ S} (hp : UniversallyOConnected p) (e : S ⟶ X) (he : e ≫ p = 𝟙 S)
    {q : Y ⟶ S} (f : X ⟶ Y) (hf : f ≫ q = p)
    {V : Scheme.{u}} (u : V ⟶ Y) [IsOpenImmersion u] [IsAffine V]
    (hrange : Set.range f.base ⊆ Set.range u.base) :
    ∃ sec : S ⟶ Y, sec ≫ q = 𝟙 S ∧ f = p ≫ sec := by
  refine ⟨e ≫ f, by rw [Category.assoc, hf, he], ?_⟩
  set f' : X ⟶ V := IsOpenImmersion.lift u f hrange with hf'
  have hfac : f' ≫ u = f := IsOpenImmersion.lift_fac u f hrange
  -- `X` is the pullback of `p` along `𝟙 S`
  set i : X ⟶ pullback p (𝟙 S) := pullback.lift (𝟙 X) p (by simp) with hi
  have hip : i ≫ pullback.snd p (𝟙 S) = p := by
    rw [hi]; exact pullback.lift_snd _ _ _
  have hiso : IsIso i := by
    refine ⟨⟨pullback.fst p (𝟙 S), ?_, ?_⟩⟩
    · rw [hi]; exact pullback.lift_fst _ _ _
    · apply pullback.hom_ext <;>
        simp [hi, pullback.lift_fst, pullback.lift_snd, pullback.condition]
  -- the affine core applied over `g := 𝟙 S`
  obtain ⟨h, hh, -⟩ := exists_unique_factor_of_isAffine hp (𝟙 S) (inv i ≫ f')
  have hf'p : f' = p ≫ h :=
    (IsIso.hom_inv_id_assoc i f').symm.trans ((congrArg (i ≫ ·) hh).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ h) hip)))
  -- assemble: `f = p ≫ (h ≫ u)` and `h ≫ u = e ≫ f`
  have hfeq : f = p ≫ (h ≫ u) := by rw [← hfac, hf'p, Category.assoc]
  have huf : e ≫ f = h ≫ u :=
    (congrArg (e ≫ ·) hfeq).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (h ≫ u)) he).trans (Category.id_comp _)))
  rw [huf]
  exact hfeq

/-- **(T-W7.7a-R1′, GIT case 1, generalized)** Rigidity for morphisms with set-theoretically
constant image: a morphism `f : X ⟶ Y` over `S` whose topological image is a single point
(GIT's "`f(X_s)` is set-theoretically a single point", which over a one-point base says
exactly this), with `X` universally `O`-connected over `S` and carrying a section, factors
through the section `η := e ≫ f` of `Y ⟶ S`.

Two deliberate deltas against GIT's phrasing, both strengthenings (recorded on the v3 board):
the one-point-base hypothesis is dropped — the `Γ`-argument never uses it, and the general
form is what the Artinian thickening step of case 2 actually consumes — and no separatedness
of `Y ⟶ S` is needed. (The skeleton's original statement without the constant-image
hypothesis was FALSE — take `f = 𝟙 (ℙ¹)` over a field — caught at implementation.)
Source: GIT p. 115, case 1 (verbatim in quotes file). -/
theorem rigidity_of_subsingleton_range {X Y S : Scheme.{u}}
    {p : X ⟶ S} (hp : UniversallyOConnected p) (e : S ⟶ X) (he : e ≫ p = 𝟙 S)
    {q : Y ⟶ S} (f : X ⟶ Y) (hf : f ≫ q = p)
    (hone : Set.Subsingleton (Set.range f.base)) :
    ∃ sec : S ⟶ Y, sec ≫ q = 𝟙 S ∧ f = p ≫ sec := by
  by_cases hX : IsEmpty X
  · haveI := hX
    exact ⟨e ≫ f, by rw [Category.assoc, hf, he], isInitialOfIsEmpty.hom_ext _ _⟩
  rw [not_isEmpty_iff] at hX
  obtain ⟨x₀⟩ := hX
  exact rigidity_of_range_le_affine hp e he f hf
    (Y.affineCover.f (Y.affineCover.idx (f.base x₀)))
    (fun y hy => by
      rw [hone hy ⟨x₀, rfl⟩]
      exact Y.affineCover.covers (f.base x₀))

/-- **(T-W7.r2 prep)** Universal `O`-connectedness is stable under base change: the second
projection of the pullback along any `g : T ⟶ S` is universally `O`-connected over `T`
(pasting of pullbacks). The rigidity lemma instantiates this at the Artinian thickenings
`Spec (O_{S,t}/𝔪ₜⁿ) ⟶ S` and at `Spec κ(s) ⟶ S` for the seed fibre. -/
theorem UniversallyOConnected.baseChange {X S : Scheme.{u}} {p : X ⟶ S}
    (hp : UniversallyOConnected p) {T : Scheme.{u}} (g : T ⟶ S) :
    UniversallyOConnected (pullback.snd p g) := by
  intro T' g' U
  rw [← pullbackLeftPullbackSndIso_hom_snd p g g', Scheme.Hom.comp_app]
  haveI h1 : IsIso ((pullbackLeftPullbackSndIso p g g').hom) :=
    (pullbackLeftPullbackSndIso p g g').isIso_hom
  haveI h2 : IsIso ((pullbackLeftPullbackSndIso p g g').hom.app
      (pullback.snd p (g' ≫ g) ⁻¹ᵁ U)) := inferInstance
  exact IsIso.comp_isIso' (hp (g' ≫ g) U) h2

/-! ### The r2 leaf decomposition (coordinator §2, 2026-07-07)

`Z := eqLocus` is the agreement locus of `f` and the constant comparison `p ≫ e ≫ f`, as
the underlying scheme of the `Over S`-equalizer; its structure morphism to `X` is a closed
immersion because `q` is separated (mathlib `isClosedImmersion_equalizer_ι_left`). The
proof of `rigidity` is assembled from three sorried leaves below (seed · Krull
neighbourhood · clopen glue), each independently attackable. -/

section EqLocus

variable {X Y S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S} [IsSeparated q]
  (f g : X ⟶ Y) (hf : f ≫ q = p) (hg : g ≫ q = p)

/-- **(T-W7.r2·a)** The agreement locus of two `S`-morphisms `f, g : X ⟶ Y` with separated
`q : Y ⟶ S`: the underlying scheme of the equalizer in `Over S`. A REAL construction (no
data-sorry): the `Over S`-equalizer exists since `Scheme` has finite limits. -/
instance : IsSeparated (Over.mk q).hom := inferInstanceAs (IsSeparated q)

noncomputable def eqLocus : Scheme.{u} :=
  (equalizer (Over.homMk f hf : Over.mk p ⟶ Over.mk q) (Over.homMk g hg)).left

/-- **(T-W7.r2·a)** The closed immersion from the agreement locus. -/
noncomputable def eqLocusι : eqLocus f g hf hg ⟶ X :=
  (equalizer.ι (Over.homMk f hf : Over.mk p ⟶ Over.mk q) (Over.homMk g hg)).left

instance : IsClosedImmersion (eqLocusι f g hf hg) :=
  isClosedImmersion_equalizer_ι_left _ _

/-- **(T-W7.r2·a)** The two morphisms agree on the agreement locus. -/
theorem eqLocusι_comp_eq : eqLocusι f g hf hg ≫ f = eqLocusι f g hf hg ≫ g := by
  have h := equalizer.condition (Over.homMk f hf : Over.mk p ⟶ Over.mk q) (Over.homMk g hg)
  exact congrArg CategoryTheory.CommaMorphism.left h

/-- **(T-W7.r2·a)** Universal property in consumable form: any test morphism equalizing
`f` and `g` factors (uniquely, but existence is what the seed/thickening steps use)
through the agreement locus. -/
theorem exists_factor_eqLocus {W : Scheme.{u}} (τ : W ⟶ X) (hτ : τ ≫ f = τ ≫ g) :
    ∃ w : W ⟶ eqLocus f g hf hg, w ≫ eqLocusι f g hf hg = τ := by
  refine ⟨(equalizer.lift (f := (Over.homMk f hf : Over.mk p ⟶ Over.mk q))
    (g := Over.homMk g hg) (Over.homMk (U := Over.mk (τ ≫ p)) τ rfl)
    (by ext; exact hτ)).left, ?_⟩
  have h := equalizer.lift_ι (f := (Over.homMk f hf : Over.mk p ⟶ Over.mk q))
    (g := Over.homMk g hg) (Over.homMk (U := Over.mk (τ ≫ p)) τ rfl) (by ext; exact hτ)
  exact congrArg CategoryTheory.CommaMorphism.left h

end EqLocus

/-- **(T-W7.r2·c·ii, the ring-level Krull engine)** A finitely generated ideal whose every
element is annihilated by some element outside a prime admits a single annihilator outside
the prime. This turns stalkwise vanishing of the equalizer ideal (supplied by Krull
intersection on the noetherian stalk) into vanishing on a basic open around the point. -/
theorem _root_.Ideal.exists_notMem_mul_eq_zero_of_fg {R : Type*} [CommRing R]
    {I : Ideal R} (hI : I.FG) {𝔭 : Ideal R} [𝔭.IsPrime]
    (h : ∀ a ∈ I, ∃ s ∉ 𝔭, s * a = 0) :
    ∃ s ∉ 𝔭, ∀ a ∈ I, s * a = 0 := by
  obtain ⟨T, hT⟩ := hI
  choose sf hsf hzero using fun a (ha : a ∈ (T : Set R)) => h a (hT ▸ Ideal.subset_span ha)
  classical
  refine ⟨∏ a ∈ T.attach, sf a.1 a.2, fun hmem => ?_, fun a ha => ?_⟩
  · obtain ⟨⟨a, haT⟩, -, hpa⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hsf a haT hpa
  · rw [← hT] at ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
      calc (∏ b ∈ T.attach, sf b.1 b.2) * x
          = (∏ b ∈ T.attach.erase ⟨x, hx⟩, sf b.1 b.2) * (sf x hx * x) := by
            rw [← Finset.prod_erase_mul T.attach _ (Finset.mem_attach T ⟨x, hx⟩)]
            ring
        _ = 0 := by rw [hzero x hx, mul_zero]
    | zero => rw [mul_zero]
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul c x _ hx =>
      rw [smul_eq_mul, show (∏ b ∈ T.attach, sf b.1 b.2) * (c * x) =
        c * ((∏ b ∈ T.attach, sf b.1 b.2) * x) by ring, hx, mul_zero]

section RigidityLeaves

variable {X Y S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S} [IsSeparated q]

/-- **(T-W7.r2·b, the seed — SORRIED LEAF)** Case 1 over `Spec κ(s)`: if `f` collapses the
fibre over `s` set-theoretically, then the fibre is contained in the agreement locus of
`f` and `p ≫ (e ≫ f)`. Attack route (all names verified at the pin): base-change the whole
situation along `S.fromSpecResidueField s` (`UniversallyOConnected.baseChange`, section
`pullback.lift (fromSpecResidueField ≫ e) (𝟙 _)`); the collapsed image lies in an affine
chart `V` of `Y` with `V ×_S Spec κ(s)` affine, so `rigidity_of_range_le_affine` applies;
push the resulting equality into `exists_factor_eqLocus` and take ranges — the fibre is the
range of `pullback.fst p (S.fromSpecResidueField s)` (mathlib pullback-carrier API). -/
theorem fibre_subset_eqLocus_of_collapsed (hp : UniversallyOConnected p)
    (e : S ⟶ X) (he : e ≫ p = 𝟙 S) (f : X ⟶ Y) (hf : f ≫ q = p) (s : S)
    (hs : Set.Subsingleton (f.base '' (p.base ⁻¹' {s}))) :
    p.base ⁻¹' {s} ⊆ Set.range (eqLocusι f (p ≫ (e ≫ f)) hf
      (by rw [Category.assoc, Category.assoc, hf, he]; exact Category.comp_id p)).base := by
  -- notation: everything is base-changed along the residue-field point of `s`
  have hFcond : (pullback.fst p (S.fromSpecResidueField s) ≫ f) ≫ q =
      pullback.snd p (S.fromSpecResidueField s) ≫ S.fromSpecResidueField s := by
    rw [Category.assoc, hf]
    exact pullback.condition
  have heTcond : (S.fromSpecResidueField s ≫ e) ≫ p =
      𝟙 (Spec (S.residueField s)) ≫ S.fromSpecResidueField s := by
    rw [Category.assoc, he, Category.comp_id, Category.id_comp]
  -- the comparison morphism over `Spec κ(s)`, and the section
  obtain ⟨F, hFρ, hFqT⟩ : ∃ F : pullback p (S.fromSpecResidueField s) ⟶
      pullback q (S.fromSpecResidueField s),
      F ≫ pullback.fst q (S.fromSpecResidueField s) =
        pullback.fst p (S.fromSpecResidueField s) ≫ f ∧
      F ≫ pullback.snd q (S.fromSpecResidueField s) =
        pullback.snd p (S.fromSpecResidueField s) :=
    ⟨pullback.lift _ _ hFcond, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨eT, heTπ, heTpT⟩ : ∃ eT : Spec (S.residueField s) ⟶
      pullback p (S.fromSpecResidueField s),
      eT ≫ pullback.fst p (S.fromSpecResidueField s) = S.fromSpecResidueField s ≫ e ∧
      eT ≫ pullback.snd p (S.fromSpecResidueField s) = 𝟙 _ :=
    ⟨pullback.lift _ _ heTcond, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  -- every point of the base-changed total space lies over the fibre of `s`
  have hπland : ∀ z, (pullback.fst p (S.fromSpecResidueField s)).base z ∈
      p.base ⁻¹' {s} := by
    intro z
    have hz : (pullback.fst p (S.fromSpecResidueField s)).base z ∈
        Set.range (pullback.fst p (S.fromSpecResidueField s)).base := ⟨z, rfl⟩
    rw [show Set.range (pullback.fst p (S.fromSpecResidueField s)).base =
        p.base ⁻¹' Set.range (S.fromSpecResidueField s).base from
      Scheme.Pullback.range_fst p (S.fromSpecResidueField s),
      Scheme.range_fromSpecResidueField] at hz
    exact hz
  -- the base-changed morphism has subsingleton range: the first projection of the
  -- residue-field base change is a preimmersion, hence injective, and it carries the
  -- range into the collapsed image `f(p⁻¹(s))`
  have hone : Set.Subsingleton (Set.range F.base) := by
    rintro _ ⟨z₁, rfl⟩ _ ⟨z₂, rfl⟩
    apply (Scheme.Hom.isEmbedding (pullback.fst q (S.fromSpecResidueField s))).injective
    have h₁ : (pullback.fst q (S.fromSpecResidueField s)).base (F.base z₁) =
        f.base ((pullback.fst p (S.fromSpecResidueField s)).base z₁) :=
      congrArg (fun m : pullback p (S.fromSpecResidueField s) ⟶ Y => m.base z₁) hFρ
    have h₂ : (pullback.fst q (S.fromSpecResidueField s)).base (F.base z₂) =
        f.base ((pullback.fst p (S.fromSpecResidueField s)).base z₂) :=
      congrArg (fun m : pullback p (S.fromSpecResidueField s) ⟶ Y => m.base z₂) hFρ
    rw [h₁, h₂]
    exact hs ⟨_, hπland z₁, rfl⟩ ⟨_, hπland z₂, rfl⟩
  -- GIT case 1 over the residue field
  obtain ⟨sec, -, hFsec⟩ := rigidity_of_subsingleton_range
    (hp.baseChange (S.fromSpecResidueField s)) eT heTpT F hFqT hone
  -- the two composites agree on the base-changed total space
  have hsec' : sec = eT ≫ F := by
    have h1 : eT ≫ F = eT ≫ (pullback.snd p (S.fromSpecResidueField s) ≫ sec) :=
      congrArg (eT ≫ ·) hFsec
    have h2 : eT ≫ (pullback.snd p (S.fromSpecResidueField s) ≫ sec) =
        (eT ≫ pullback.snd p (S.fromSpecResidueField s)) ≫ sec :=
      (Category.assoc _ _ _).symm
    rw [h1, h2, heTpT, Category.id_comp]
  have hπeq : pullback.fst p (S.fromSpecResidueField s) ≫ f =
      pullback.fst p (S.fromSpecResidueField s) ≫ (p ≫ (e ≫ f)) := by
    calc pullback.fst p (S.fromSpecResidueField s) ≫ f
        = F ≫ pullback.fst q (S.fromSpecResidueField s) := hFρ.symm
      _ = (pullback.snd p (S.fromSpecResidueField s) ≫ sec) ≫
          pullback.fst q (S.fromSpecResidueField s) :=
        congrArg (· ≫ pullback.fst q (S.fromSpecResidueField s)) hFsec
      _ = pullback.snd p (S.fromSpecResidueField s) ≫ (eT ≫ F) ≫
          pullback.fst q (S.fromSpecResidueField s) := by
        rw [hsec']
        simp only [Category.assoc]
      _ = pullback.snd p (S.fromSpecResidueField s) ≫ eT ≫
          (pullback.fst p (S.fromSpecResidueField s) ≫ f) := by
        rw [← hFρ]
        simp only [Category.assoc]
      _ = pullback.snd p (S.fromSpecResidueField s) ≫ (S.fromSpecResidueField s ≫ e) ≫ f := by
        rw [← Category.assoc eT, heTπ]
      _ = (pullback.snd p (S.fromSpecResidueField s) ≫ S.fromSpecResidueField s) ≫ e ≫ f := by
        simp only [Category.assoc]
      _ = (pullback.fst p (S.fromSpecResidueField s) ≫ p) ≫ e ≫ f := by
        rw [pullback.condition]
      _ = pullback.fst p (S.fromSpecResidueField s) ≫ (p ≫ (e ≫ f)) := by
        simp only [Category.assoc]
  -- factor through the agreement locus and take ranges
  obtain ⟨w, hw⟩ := exists_factor_eqLocus f (p ≫ (e ≫ f)) hf
    (by rw [Category.assoc, Category.assoc, hf, he]; exact Category.comp_id p)
    (pullback.fst p (S.fromSpecResidueField s)) hπeq
  intro x hx
  have hxr : x ∈ Set.range (pullback.fst p (S.fromSpecResidueField s)).base := by
    rw [show Set.range (pullback.fst p (S.fromSpecResidueField s)).base =
        p.base ⁻¹' Set.range (S.fromSpecResidueField s).base from
      Scheme.Pullback.range_fst p (S.fromSpecResidueField s),
      Scheme.range_fromSpecResidueField]
    exact hx
  obtain ⟨z, hz⟩ := hxr
  refine ⟨w.base z, ?_⟩
  have hwz := congrArg (fun m : pullback p (S.fromSpecResidueField s) ⟶ X => m.base z) hw
  simpa using hwz.trans hz

/-- **(T-W7.r2·c, vanishing-locus openness)** On a locally noetherian scheme, the locus
where a quasi-coherent ideal datum has zero stalk-image over a fixed affine is open: if
every generator's germ dies at `x`, the finitely many annihilators multiply to a single
`s ∉ 𝔭ₓ` (`Ideal.exists_notMem_mul_eq_zero_of_fg`), and on `X.basicOpen s ∋ x` the germs
of the whole ideal vanish. -/
theorem isOpen_germMap_ideal_eq_bot {X : Scheme.{u}} [IsLocallyNoetherian X]
    (U : X.affineOpens) (I : Ideal Γ(X, U.1)) :
    IsOpen {z : X | ∃ hz : z ∈ U.1,
      Ideal.map (X.presheaf.germ U.1 z hz).hom I = ⊥} := by
  rw [isOpen_iff_forall_mem_open]
  rintro z ⟨hz, hbot⟩
  haveI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  -- the stalk at `z` is the localization of `Γ(U)` at the prime of `z`
  letI := X.presheaf.algebra_section_stalk ⟨z, hz⟩
  haveI hloc := U.2.isLocalization_stalk ⟨z, hz⟩
  have halg : algebraMap Γ(X, U.1) (X.presheaf.stalk z) =
      (X.presheaf.germ U.1 z hz).hom := rfl
  -- engine input: every element of `I` is annihilated away from the prime of `z`
  have hann : ∀ a ∈ I, ∃ s ∉ (U.2.primeIdealOf ⟨z, hz⟩).asIdeal, s * a = 0 := by
    intro a ha
    have hgerm : (X.presheaf.germ U.1 z hz).hom a = 0 := by
      have : (X.presheaf.germ U.1 z hz).hom a ∈
          Ideal.map (X.presheaf.germ U.1 z hz).hom I := Ideal.mem_map_of_mem _ ha
      rw [hbot] at this
      simpa using this
    have := (IsLocalization.map_eq_zero_iff
      (U.2.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl
      (X.presheaf.stalk z) a).mp (by rwa [halg])
    obtain ⟨⟨s, hs⟩, hsa⟩ := this
    exact ⟨s, hs, hsa⟩
  obtain ⟨s, hs, hskill⟩ := Ideal.exists_notMem_mul_eq_zero_of_fg
    (IsNoetherian.noetherian I) hann
  -- the basic open of the common annihilator is the required neighbourhood
  refine ⟨X.basicOpen s, fun w hw => ?_, (X.basicOpen s).2, ?_⟩
  · have hwU : w ∈ U.1 := X.basicOpen_le s hw
    refine ⟨hwU, ?_⟩
    have hunit : IsUnit ((X.presheaf.germ U.1 w hwU).hom s) :=
      (Scheme.mem_basicOpen X s w hwU).mp hw
    rw [eq_bot_iff, Ideal.map_le_iff_le_comap]
    intro a ha
    have : (X.presheaf.germ U.1 w hwU).hom (s * a) = 0 := by rw [hskill a ha, map_zero]
    rw [map_mul] at this
    simpa [hunit.mul_right_eq_zero] using this
  · have hmem : z ∈ X.basicOpen s := by
      rw [Scheme.mem_basicOpen X s z hz]
      have := IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk z)
        (U.2.primeIdealOf ⟨z, hz⟩).asIdeal s
      rw [halg] at this
      exact this.mpr hs
    exact hmem

/-- **(T-W7.r2·c, cross-affine germ vanishing)** If some affine chart at `w` kills the
ideal datum's germs, then EVERY chart does: refine both charts to a common basic open
(`exists_basicOpen_le_affine_inter`) where the two presentations of the ideal agree
(the `map_ideal_basicOpen` field, both sides), and push germs through `germ_res`. -/
theorem germ_ideal_eq_zero_of_exists_affine {X : Scheme.{u}}
    (K : Scheme.IdealSheafData X) (w : X)
    (hW : ∃ U' : X.affineOpens, ∃ hw : w ∈ U'.1,
      Ideal.map (X.presheaf.germ U'.1 w hw).hom (K.ideal U') = ⊥)
    (U : X.affineOpens) (hwU : w ∈ U.1) {a : Γ(X, U.1)} (ha : a ∈ K.ideal U) :
    (X.presheaf.germ U.1 w hwU).hom a = 0 := by
  obtain ⟨U', hwU', hbot'⟩ := hW
  obtain ⟨r, r', hrr', hwr⟩ := exists_basicOpen_le_affine_inter U.2 U'.2 w ⟨hwU, hwU'⟩
  have hVU : X.affineBasicOpen r ≤ U := X.basicOpen_le r
  have hVU' : X.affineBasicOpen r ≤ U' := by
    show X.basicOpen r ≤ U'.1
    rw [hrr']
    exact X.basicOpen_le r'
  rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (hVU : _ ≤ U.1)) w hwr a]
  have h1 : (X.presheaf.map (homOfLE (hVU : _ ≤ U.1)).op).hom a ∈
      K.ideal (X.affineBasicOpen r) := by
    rw [← K.map_ideal hVU]
    exact Ideal.mem_map_of_mem _ ha
  have h2 : Ideal.map (X.presheaf.germ (X.affineBasicOpen r).1 w hwr).hom
      (K.ideal (X.affineBasicOpen r)) = ⊥ := by
    rw [← K.map_ideal hVU', Ideal.map_map]
    have hcomp : ((X.presheaf.germ (X.affineBasicOpen r).1 w hwr).hom).comp
        (X.presheaf.map (homOfLE (hVU' : _ ≤ U'.1)).op).hom =
        (X.presheaf.germ U'.1 w hwU').hom :=
      congrArg CommRingCat.Hom.hom
        (TopCat.Presheaf.germ_res X.presheaf (homOfLE (hVU' : _ ≤ U'.1)) w hwr)
    rw [hcomp, hbot']
  have h3 := h2 ▸ Ideal.mem_map_of_mem (X.presheaf.germ (X.affineBasicOpen r).1 w hwr).hom h1
  exact Ideal.mem_bot.mp h3

set_option backward.isDefEq.respectTransparency.types false in
/-- **(T-W7.r2·c, generic stalk-evaluation)** If a section dies under the `Spec`-point of
the stalk twisted by any ring map `φ` out of the stalk, then its germ dies under `φ`:
`(Spec.map φ ≫ fromSpecStalk).app` is `germ` followed by `φ` up to isomorphisms — the
`ΓSpecIso` and a restriction along an equality of opens (every open of the local `Spec` of
the stalk containing the closed point is `⊤`). Stated for an abstract `B` so that
elaboration never unfolds a concrete quotient ring. -/
theorem germ_eq_zero_of_fromSpecStalk_app {X : Scheme.{u}} {U : X.Opens} {x : X}
    (hxU : x ∈ U) {B : CommRingCat.{u}} (φ : X.presheaf.stalk x ⟶ B)
    (a : Γ(X, U)) (h : (((Spec.map φ ≫ X.fromSpecStalk x)).app U).hom a = 0) :
    φ.hom ((X.presheaf.germ U x hxU).hom a) = 0 := by
  have hcp : IsLocalRing.closedPoint (X.presheaf.stalk x) ∈ (X.fromSpecStalk x) ⁻¹ᵁ U := by
    show (X.fromSpecStalk x).base _ ∈ U
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hxU
  have hV' : (X.fromSpecStalk x) ⁻¹ᵁ U = ⊤ := IsLocalRing.closed_point_mem_iff.mp hcp
  have hτapp : (Spec.map φ ≫ X.fromSpecStalk x).app U = X.presheaf.germ U x hxU ≫
      φ ≫ (Scheme.ΓSpecIso B).inv ≫ (Spec B).presheaf.map
        ((TopologicalSpace.Opens.map (Spec.map φ).base).map
          (homOfLE (le_top : (X.fromSpecStalk x) ⁻¹ᵁ U ≤ ⊤)).op.unop).op := by
    rw [Scheme.Hom.comp_app, Scheme.fromSpecStalk_app hxU]
    simp only [Category.assoc]
    congr 1
    rw [Scheme.Hom.naturality (f := Spec.map φ) ((homOfLE le_top).op),
      show (Spec.map φ).app ⊤ = (Spec.map φ).appTop from rfl,
      Scheme.ΓSpecIso_inv_naturality_assoc]
    rfl
  rw [hτapp] at h
  have hmapped : (TopologicalSpace.Opens.map (Spec.map φ).base).obj
      ((X.fromSpecStalk x) ⁻¹ᵁ U) = ⊤ := by
    rw [hV']
    rfl
  haveI hI1 : IsIso ((TopologicalSpace.Opens.map (Spec.map φ).base).map
      (homOfLE (le_top : (X.fromSpecStalk x) ⁻¹ᵁ U ≤ ⊤)).op.unop) :=
    ⟨⟨homOfLE hmapped.ge, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  haveI hI2 : IsIso (((TopologicalSpace.Opens.map (Spec.map φ).base).map
      (homOfLE (le_top : (X.fromSpecStalk x) ⁻¹ᵁ U ≤ ⊤)).op.unop).op) := inferInstance
  haveI hI3 : IsIso ((Spec B).presheaf.map
      ((TopologicalSpace.Opens.map (Spec.map φ).base).map
        (homOfLE (le_top : (X.fromSpecStalk x) ⁻¹ᵁ U ≤ ⊤)).op.unop).op) := inferInstance
  have hinj : Function.Injective (((Scheme.ΓSpecIso B).inv ≫
      (Spec B).presheaf.map
        ((TopologicalSpace.Opens.map (Spec.map φ).base).map
          (homOfLE (le_top : (X.fromSpecStalk x) ⁻¹ᵁ U ≤ ⊤)).op.unop).op).hom) :=
    ((ConcreteCategory.isIso_iff_bijective _).mp
      (IsIso.comp_isIso' inferInstance hI3)).injective
  apply hinj
  first
  | simpa using h
  | (rw [map_zero]; simpa using h)
  | (rw [map_zero]; simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h ⊢; exact h)

set_option backward.isDefEq.respectTransparency.types false in
/-- **(T-W7.r2·c·i — SORRIED SUB-LEAF, the one remaining gap of `rigidity`)** Sections of
the equalizer ideal die in every infinitesimal neighbourhood of a collapsed fibre: if the
fibre over `t := p x` lies set-theoretically in the agreement locus, then the germ at `x`
of any section of `(eqLocusι f g hf hg).ker` lies in `(𝔪_{p x}·O_{X,x})ⁿ` for every `n`.
Route (all names verified at the pin; board ticket has the full map): case 1 over
`Spec (Γstalk (p x) ⧸ 𝔪ⁿ)` factors the thickened fibre through the locus — the
`fromSpecStalk`-composite is a preimmersion, so the r2·b subsingleton mechanism applies
verbatim; then push `a` along `Scheme.stalkMap_germ` at a preimage point
(`Scheme.Pullback.range_fst`), and compute the kernel affine-locally via `pullbackSpecIso`
(`Γ(U) ⊗ (stalk/𝔪ⁿ)`; `IsLocalization` torsion + `Ideal.map` extension — no
stalk-of-pullback API needed). -/
theorem germ_ker_mem_pow_of_fibre_subset [IsLocallyNoetherian S] [IsProper p]
    (hp : UniversallyOConnected p) (e : S ⟶ X) (he : e ≫ p = 𝟙 S)
    (f g : X ⟶ Y) (hf : f ≫ q = p) (hg : g ≫ q = p)
    (hgconst : g = p ≫ (e ≫ f))
    (x : X) (hset : p.base ⁻¹' {p.base x} ⊆ Set.range (eqLocusι f g hf hg).base)
    (U : X.affineOpens) (hxU : x ∈ U.1) (a : Γ(X, U.1))
    (ha : a ∈ (eqLocusι f g hf hg).ker.ideal U) (n : ℕ) :
    X.presheaf.germ U.1 x hxU a ∈
      (Ideal.map (p.stalkMap x).hom
        (IsLocalRing.maximalIdeal (S.presheaf.stalk (p.base x)))) ^ n := by
  subst hgconst
  rcases n with - | n
  · simp
  -- the (n+1)-st infinitesimal neighbourhood of `p x`, as a scheme over `S`
  set gT : Spec (CommRingCat.of (S.presheaf.stalk (p.base x) ⧸
      (IsLocalRing.maximalIdeal (S.presheaf.stalk (p.base x))) ^ (n + 1))) ⟶ S :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ S.fromSpecStalk (p.base x) with hgT
  -- its range is contained in the single point `p x` (SORRIED micro-leaf: the quotient's
  -- primes all contain the maximal ideal, so `Spec.map` hits only the closed point, which
  -- `fromSpecStalk` sends to `p x`; names: `PrimeSpectrum.range_comap_of_surjective`,
  -- `Ideal.IsPrime.pow_le_iff`, `IsLocalRing.closedPoint`, `fromSpecStalk_closedPoint`)
  have hrange_gT : Set.range gT.base ⊆ {p.base x} := by
    rw [hgT]
    rintro _ ⟨z, rfl⟩
    have hz : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal (S.presheaf.stalk (p.base x))) ^ (n + 1))))).base z =
        IsLocalRing.closedPoint (S.presheaf.stalk (p.base x)) := by
      have hmem : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          ((IsLocalRing.maximalIdeal (S.presheaf.stalk (p.base x))) ^ (n + 1))))).base z ∈
          Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk
            ((IsLocalRing.maximalIdeal (S.presheaf.stalk (p.base x))) ^ (n + 1)))) :=
        ⟨z, rfl⟩
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
        Ideal.mk_ker] at hmem
      have hle0 : (IsLocalRing.maximalIdeal (S.presheaf.stalk (p.base x))) ^ (n + 1) ≤
          ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
            ((IsLocalRing.maximalIdeal (S.presheaf.stalk (p.base x))) ^ (n + 1))))).base
              z).asIdeal := by
        have hsub := (PrimeSpectrum.mem_zeroLocus _ _).mp hmem
        exact fun y hy => hsub hy
      have hle : IsLocalRing.maximalIdeal (S.presheaf.stalk (p.base x)) ≤
          ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
            ((IsLocalRing.maximalIdeal (S.presheaf.stalk (p.base x))) ^ (n + 1))))).base
              z).asIdeal :=
        Ideal.IsPrime.le_of_pow_le hle0
      exact (PrimeSpectrum.ext ((IsLocalRing.maximalIdeal.isMaximal _).eq_of_le
        (Ideal.IsPrime.ne_top inferInstance) hle)).symm
    rw [Scheme.Hom.comp_apply, hz, Scheme.fromSpecStalk_closedPoint]
    rfl
  haveI hpre : IsPreimmersion gT := by
    rw [hgT]
    infer_instance
  have hFcond : (pullback.fst p gT ≫ f) ≫ q = pullback.snd p gT ≫ gT := by
    rw [Category.assoc, hf]
    exact pullback.condition
  obtain ⟨F, hFρ, hFqT⟩ : ∃ F : pullback p gT ⟶ pullback q gT,
      F ≫ pullback.fst q gT = pullback.fst p gT ≫ f ∧
      F ≫ pullback.snd q gT = pullback.snd p gT :=
    ⟨pullback.lift _ _ hFcond, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have heTcond : (gT ≫ e) ≫ p = 𝟙 _ ≫ gT := by
    rw [Category.assoc, he, Category.comp_id, Category.id_comp]
  obtain ⟨eT, heTπ, heTpT⟩ : ∃ eT, eT ≫ pullback.fst p gT = gT ≫ e ∧
      eT ≫ pullback.snd p gT = 𝟙 _ :=
    ⟨pullback.lift _ _ heTcond, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hπland : ∀ z, (pullback.fst p gT).base z ∈ p.base ⁻¹' {p.base x} := by
    intro z
    have hz : (pullback.fst p gT).base z ∈ Set.range (pullback.fst p gT).base := ⟨z, rfl⟩
    rw [Scheme.Pullback.range_fst] at hz
    exact hrange_gT (Set.mem_preimage.mp hz)
  -- the collapse: on the fibre over `p x`, `f` agrees with the constant through the locus
  have hs : Set.Subsingleton (f.base '' (p.base ⁻¹' {p.base x})) := by
    have hval : ∀ z ∈ p.base ⁻¹' {p.base x},
        f.base z = (e ≫ f).base (p.base x) := by
      intro z hz
      obtain ⟨y, hy⟩ := hset hz
      have hc := congrArg
        (fun m : eqLocus f (p ≫ (e ≫ f)) hf hg ⟶ Y => m.base y)
        (eqLocusι_comp_eq f (p ≫ (e ≫ f)) hf hg)
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at hc
      rw [hy] at hc
      rw [hc]
      have hpz : p.base z = p.base x := hz
      simp [Scheme.Hom.comp_base, hpz]
    rintro _ ⟨z₁, hz₁, rfl⟩ _ ⟨z₂, hz₂, rfl⟩
    rw [hval z₁ hz₁, hval z₂ hz₂]
  have hone : Set.Subsingleton (Set.range F.base) := by
    rintro _ ⟨z₁, rfl⟩ _ ⟨z₂, rfl⟩
    apply (Scheme.Hom.isEmbedding (pullback.fst q gT)).injective
    have h₁ : (pullback.fst q gT).base (F.base z₁) =
        f.base ((pullback.fst p gT).base z₁) :=
      congrArg (fun m : pullback p gT ⟶ Y => m.base z₁) hFρ
    have h₂ : (pullback.fst q gT).base (F.base z₂) =
        f.base ((pullback.fst p gT).base z₂) :=
      congrArg (fun m : pullback p gT ⟶ Y => m.base z₂) hFρ
    rw [h₁, h₂]
    exact hs ⟨_, hπland z₁, rfl⟩ ⟨_, hπland z₂, rfl⟩
  obtain ⟨sec, -, hFsec⟩ := rigidity_of_subsingleton_range
    (hp.baseChange gT) eT heTpT F hFqT hone
  have hsec' : sec = eT ≫ F := by
    have h1 : eT ≫ F = eT ≫ (pullback.snd p gT ≫ sec) := congrArg (eT ≫ ·) hFsec
    have h2 : eT ≫ (pullback.snd p gT ≫ sec) = (eT ≫ pullback.snd p gT) ≫ sec :=
      (Category.assoc _ _ _).symm
    rw [h1, h2, heTpT, Category.id_comp]
  have hπeq : pullback.fst p gT ≫ f = pullback.fst p gT ≫ (p ≫ (e ≫ f)) := by
    calc pullback.fst p gT ≫ f
        = F ≫ pullback.fst q gT := hFρ.symm
      _ = (pullback.snd p gT ≫ sec) ≫ pullback.fst q gT :=
        congrArg (· ≫ pullback.fst q gT) hFsec
      _ = pullback.snd p gT ≫ (eT ≫ F) ≫ pullback.fst q gT := by
        rw [hsec']
        simp only [Category.assoc]
      _ = pullback.snd p gT ≫ eT ≫ (pullback.fst p gT ≫ f) := by
        rw [← hFρ]
        simp only [Category.assoc]
      _ = pullback.snd p gT ≫ (gT ≫ e) ≫ f := by
        rw [← Category.assoc eT, heTπ]
      _ = (pullback.snd p gT ≫ gT) ≫ e ≫ f := by
        simp only [Category.assoc]
      _ = (pullback.fst p gT ≫ p) ≫ e ≫ f := by
        rw [pullback.condition]
      _ = pullback.fst p gT ≫ (p ≫ (e ≫ f)) := by
        simp only [Category.assoc]
  -- the thickened fibre factors through the agreement locus
  obtain ⟨w, hw⟩ := exists_factor_eqLocus f (p ≫ (e ≫ f)) hf hg
    (pullback.fst p gT) hπeq
  -- the section dies in the sections of the thickened fibre over `U`
  have hι0 : (((eqLocusι f (p ≫ (e ≫ f)) hf hg)).app U.1).hom a = 0 := by
    have hker := Scheme.Hom.ker_apply (eqLocusι f (p ≫ (e ≫ f)) hf hg) U
    rw [hker] at ha
    exact ha
  -- the direct thickened point: `Spec` of the stalk quotient, mapping into `X` through
  -- `fromSpecStalk`; it lifts into the thickened fibre by `fromSpecStalk`-naturality,
  -- hence factors through the agreement locus, killing `a`'s germ mod `(𝔪·O)^{n+1}`.
  have hle : Ideal.map (p.stalkMap x).hom
      ((IsLocalRing.maximalIdeal (S.presheaf.stalk (p.base x))) ^ (n + 1)) ≤
      (Ideal.map (p.stalkMap x).hom
        (IsLocalRing.maximalIdeal (S.presheaf.stalk (p.base x)))) ^ (n + 1) :=
    le_of_eq (Ideal.map_pow _ _ _)
  set τ : Spec (CommRingCat.of ((X.presheaf.stalk x) ⧸
      (Ideal.map (p.stalkMap x).hom
        (IsLocalRing.maximalIdeal (S.presheaf.stalk (p.base x)))) ^ (n + 1))) ⟶ X :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ X.fromSpecStalk x with hτ
  have hsquare : τ ≫ p = Spec.map (CommRingCat.ofHom (Ideal.quotientMap _
      (p.stalkMap x).hom (Ideal.map_le_iff_le_comap.mp hle))) ≫ gT := by
    rw [hτ, hgT, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
  obtain ⟨ℓ, hℓτ⟩ : ∃ ℓ, ℓ ≫ pullback.fst p gT = τ :=
    ⟨pullback.lift τ _ hsquare, pullback.lift_fst _ _ _⟩
  have hτfac : τ = (ℓ ≫ w) ≫ eqLocusι f (p ≫ (e ≫ f)) hf hg := by
    rw [Category.assoc, hw, hℓτ]
  have happ : (τ.app U.1).hom a = 0 := by
    rw [Scheme.Hom.congr_app hτfac U.1]
    simp [hι0]
  -- final unpacking through the generic stalk-evaluation lemma
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  rw [hτ] at happ
  exact germ_eq_zero_of_fromSpecStalk_app hxU
    (CommRingCat.ofHom (Ideal.Quotient.mk _)) a happ
/-- **(T-W7.r2·c, Krull neighbourhood — SORRIED LEAF)** If the fibre over `t` lies
set-theoretically in the agreement locus, it lies in it scheme-theoretically on an open
`p⁻¹(U₀)`. Attack route: for every `n`, case 1 over `Spec (Γstalk/𝔪ₜⁿ)` (Artinian local,
`rigidity_of_range_le_affine` + `UniversallyOConnected.baseChange`) factors the thickened
fibre through the locus; on stalks at `x ∈ p⁻¹(t)` the ideal of the closed immersion lands
in `⋂ₙ 𝔪ₜⁿ·O_{X,x} = ⊥` (`Ideal.iInf_pow_smul_eq_bot_of_isLocalRing`; stalks noetherian —
`X` is locally noetherian via `IsProper p` over locally noetherian `S`); the ideal sheaf is
finite-type, so it vanishes on an open `W ⊇ p⁻¹(t)`; `IsProper p` (closed) turns `W` into
`p⁻¹(U₀)`. -/
theorem exists_open_factor_of_fibre_subset [IsLocallyNoetherian S] [IsProper p]
    (hp : UniversallyOConnected p) (e : S ⟶ X) (he : e ≫ p = 𝟙 S)
    (f g : X ⟶ Y) (hf : f ≫ q = p) (hg : g ≫ q = p)
    (hgconst : g = p ≫ (e ≫ f)) (t : S)
    (hset : p.base ⁻¹' {t} ⊆ Set.range (eqLocusι f g hf hg).base) :
    ∃ U₀ : S.Opens, t ∈ U₀ ∧
      ∃ w : (p ⁻¹ᵁ U₀).toScheme ⟶ eqLocus f g hf hg,
        w ≫ eqLocusι f g hf hg = (p ⁻¹ᵁ U₀).ι := by
  -- The factorization consumable is `IsClosedImmersion.lift` (ker-inclusion universal
  -- property), so the whole leaf reduces to: the equalizer ideal sheaf vanishes on a tube
  -- `p⁻¹(U₀)` — i.e. `ι.ker ≤ (tube-inclusion).ker`. That vanishing statement is the
  -- Artinian-thickening + affine-local-Krull composite (sub-route on the board ticket):
  -- (c·i) case 1 over `Spec (Γstalk t ⧸ 𝔪ⁿ)` via the r2·b preimmersion mechanism gives
  -- `ι.ker ≤ (thickened fibre).ker` for every `n`; (c·ii) affine-locally the f.g. ideal
  -- then lands in `⋂ₙ 𝔪ᵗⁿ·O_{X,x} = ⊥` (Krull), giving a basicOpen ∋ x on which it is
  -- zero; quasi-compactness of the fibre + properness produce the tube.
  have hW : ∃ U₀ : S.Opens, t ∈ U₀ ∧
      (eqLocusι f g hf hg).ker ≤ ((p ⁻¹ᵁ U₀ : X.Opens).ι).ker := by
    classical
    haveI hXnoeth : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
    -- (1) the good locus: union over affines of the germ-vanishing sets (open, proven)
    set Wset : Set X := ⋃ U : X.affineOpens, {z : X | ∃ hz : z ∈ U.1,
      Ideal.map (X.presheaf.germ U.1 z hz).hom
        ((eqLocusι f g hf hg).ker.ideal U) = ⊥} with hWset
    have hWopen : IsOpen Wset :=
      isOpen_iUnion fun U => isOpen_germMap_ideal_eq_bot U _
    -- (2) the fibre lies in the good locus: the c·i germs + Krull intersection
    have hfib : p.base ⁻¹' {t} ⊆ Wset := by
      intro x hx
      have hxt : p.base x = t := hx
      obtain ⟨U, hxU⟩ : ∃ U : X.affineOpens, x ∈ U.1 := by
        have : x ∈ (⊤ : X.Opens) := trivial
        rw [← iSup_affineOpens_eq_top X, TopologicalSpace.Opens.mem_iSup] at this
        exact this
      refine Set.mem_iUnion.mpr ⟨U, hxU, ?_⟩
      rw [eq_bot_iff, Ideal.map_le_iff_le_comap]
      intro a ha
      have hloc : IsLocalHom (p.stalkMap x).hom := inferInstance
      have hle : Ideal.map (p.stalkMap x).hom
          (IsLocalRing.maximalIdeal (S.presheaf.stalk (p.base x))) ≤
          IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
        rw [Ideal.map_le_iff_le_comap]
        intro m hm
        rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm
        exact fun hu => hm (hloc.map_nonunit m hu)
      have hpow : ∀ n, X.presheaf.germ U.1 x hxU a ∈
          (Ideal.map (p.stalkMap x).hom
            (IsLocalRing.maximalIdeal (S.presheaf.stalk (p.base x)))) ^ n :=
        fun n => germ_ker_mem_pow_of_fibre_subset hp e he f g hf hg hgconst x
          (hxt ▸ hset) U hxU a ha n
      have hbot : (⨅ n : ℕ, (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ^ n) = ⊥ :=
        Ideal.iInf_pow_eq_bot_of_isLocalRing _
          (Ideal.IsMaximal.ne_top (IsLocalRing.maximalIdeal.isMaximal _))
      have hmem : X.presheaf.germ U.1 x hxU a ∈ (⊥ : Ideal (X.presheaf.stalk x)) := by
        rw [← hbot]
        exact Ideal.mem_iInf.mpr fun n => Ideal.pow_right_mono hle n (hpow n)
      simpa using hmem
    -- (3) the properness tube around the fibre
    have hclosed : IsClosed (p.base '' Wsetᶜ) := p.isClosedMap _ hWopen.isClosed_compl
    refine ⟨⟨(p.base '' Wsetᶜ)ᶜ, hclosed.isOpen_compl⟩, fun hmem => ?_, ?_⟩
    · obtain ⟨x, hxW, hpx⟩ := hmem
      exact hxW (hfib (show x ∈ p.base ⁻¹' {t} from hpx))
    · -- (4) the equalizer ideal is contained in the kernel of the tube inclusion:
      -- test the restricted section by germs of the subscheme sheaf; each germ is the
      -- stalk-map image of an ambient germ (`germ_stalkMap_apply`), which dies on the
      -- good locus by the cross-affine vanishing lemma. The final `convert … using 1; rfl`
      -- crosses the `sheaf.presheaf`-vs-`presheaf` stalk spelling (defeq, but only at
      -- default transparency — `exact` fails on the coerced carriers, `rfl` closes).
      intro U a ha
      rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
      apply TopCat.Presheaf.section_ext
        ((p ⁻¹ᵁ ⟨(p.base '' Wsetᶜ)ᶜ, hclosed.isOpen_compl⟩ : X.Opens)).toScheme.sheaf
      intro v hv
      have hvW : ((p ⁻¹ᵁ ⟨(p.base '' Wsetᶜ)ᶜ, hclosed.isOpen_compl⟩ : X.Opens)).ι.base v ∈
          Wset := by
        by_contra hzW
        exact v.2 (Set.mem_image_of_mem _ hzW)
      have hvU : ((p ⁻¹ᵁ ⟨(p.base '' Wsetᶜ)ᶜ, hclosed.isOpen_compl⟩ : X.Opens)).ι.base v ∈
          U.1 := hv
      have hgermzero : (X.presheaf.germ U.1 _ hvU).hom a = 0 := by
        obtain ⟨U', hU'⟩ := Set.mem_iUnion.mp hvW
        exact germ_ideal_eq_zero_of_exists_affine _ _ ⟨U', hU'⟩ U hvU ha
      have hz : ((((p ⁻¹ᵁ ⟨(p.base '' Wsetᶜ)ᶜ, hclosed.isOpen_compl⟩ : X.Opens)).toScheme
          ).presheaf.germ
            (((p ⁻¹ᵁ ⟨(p.base '' Wsetᶜ)ᶜ, hclosed.isOpen_compl⟩ : X.Opens)).ι ⁻¹ᵁ U.1)
            v hv).hom
          ((((p ⁻¹ᵁ ⟨(p.base '' Wsetᶜ)ᶜ, hclosed.isOpen_compl⟩ : X.Opens)).ι.app U.1).hom
            a) =
          ((((p ⁻¹ᵁ ⟨(p.base '' Wsetᶜ)ᶜ, hclosed.isOpen_compl⟩ : X.Opens)).toScheme
          ).presheaf.germ
            (((p ⁻¹ᵁ ⟨(p.base '' Wsetᶜ)ᶜ, hclosed.isOpen_compl⟩ : X.Opens)).ι ⁻¹ᵁ U.1)
            v hv).hom 0 := by
        rw [map_zero]
        rw [← Scheme.Hom.germ_stalkMap_apply
          ((p ⁻¹ᵁ ⟨(p.base '' Wsetᶜ)ᶜ, hclosed.isOpen_compl⟩ : X.Opens)).ι U.1 v hv a]
        show (((p ⁻¹ᵁ ⟨(p.base '' Wsetᶜ)ᶜ,
            hclosed.isOpen_compl⟩ : X.Opens)).ι.stalkMap v).hom
          ((X.presheaf.germ U.1 _ hvU).hom a) = 0
        rw [hgermzero, map_zero]
      convert hz using 1 <;> rfl
  obtain ⟨U₀, htU₀, hker⟩ := hW
  exact ⟨U₀, htU₀, IsClosedImmersion.lift _ _ hker, IsClosedImmersion.lift_fac _ _ hker⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- **(T-W7.r2·d, clopen assembly — SORRIED LEAF)** On a connected base, if the agreement
locus contains one fibre set-theoretically and every set-theoretic fibre containment
upgrades to an open scheme-theoretic one (the Krull leaf), then the identity of `X`
factors through the locus. Attack route: `U₁ := {t | p⁻¹(t) ⊆ range ι}` contains `s`, is
open by the Krull leaf, and is closed because `U₁ = S ∖ p(X ∖ range ι)` with `p` an open
map (`UniversallyOpen.of_flat`: `Flat` + `LocallyOfFinitePresentation` from properness over
a locally noetherian base); connectedness gives `U₁ = S`; the open factorizations glue
along `⨆ = ⊤` since `eqLocusι` is a monomorphism (closed immersion), giving the global
factorization. -/
theorem exists_factor_of_forall_component [IsLocallyNoetherian S] [IsProper p] [Flat p]
    (hp : UniversallyOConnected p) (e : S ⟶ X) (he : e ≫ p = 𝟙 S)
    (f g : X ⟶ Y) (hf : f ≫ q = p) (hg : g ≫ q = p)
    (hgconst : g = p ≫ (e ≫ f))
    (hseed : ∀ t : S, ∃ s ∈ connectedComponent t,
      p.base ⁻¹' {s} ⊆ Set.range (eqLocusι f g hf hg).base) :
    ∃ w : X ⟶ eqLocus f g hf hg, w ≫ eqLocusι f g hf hg = 𝟙 X := by
  classical
  -- the locus of set-theoretic fibrewise containment
  set U₁ : Set S := {t | p.base ⁻¹' {t} ⊆ Set.range (eqLocusι f g hf hg).base} with hU₁
  -- open, by the Krull-neighbourhood leaf
  have hopen : IsOpen U₁ := by
    rw [isOpen_iff_forall_mem_open]
    intro t ht
    obtain ⟨U₀, htU₀, w₀, hw₀⟩ := exists_open_factor_of_fibre_subset hp e he f g hf hg hgconst t ht
    have hsub : ((p ⁻¹ᵁ U₀) : Set X) ⊆ Set.range (eqLocusι f g hf hg).base := by
      rintro x hx
      refine ⟨w₀.base ⟨x, hx⟩, ?_⟩
      have e5 := congrArg
        (fun m : ((p ⁻¹ᵁ U₀ : X.Opens)).toScheme ⟶ X => m.base ⟨x, hx⟩) hw₀
      simpa using e5
    exact ⟨U₀, fun t' ht' x hx => hsub (show p.base x ∈ U₀ by rw [hx]; exact ht'), U₀.2, htU₀⟩
  -- closed: the complement is the image of the open complement of the locus under open `p`
  have hclosed : IsClosed U₁ := by
    rw [← isOpen_compl_iff]
    have hcompl : U₁ᶜ = p.base '' (Set.range (eqLocusι f g hf hg).base)ᶜ := by
      ext t
      constructor
      · intro ht
        rw [Set.mem_compl_iff, hU₁, Set.mem_setOf_eq, Set.not_subset] at ht
        obtain ⟨x, hx1, hx2⟩ := ht
        exact ⟨x, hx2, hx1⟩
      · rintro ⟨x, hx, rfl⟩ h
        exact hx (h rfl)
    rw [hcompl]
    exact p.isOpenMap _
      (Scheme.Hom.isClosedEmbedding (eqLocusι f g hf hg)).isClosed_range.isOpen_compl
  -- every connected component meets the clopen locus, so it is everything
  have huniv : U₁ = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro t
    obtain ⟨s, hs_comp, hs_seed⟩ := hseed t
    exact isPreconnected_connectedComponent.subset_isClopen ⟨hclosed, hopen⟩
      ⟨s, hs_comp, hs_seed⟩ mem_connectedComponent
  -- choose a factorization neighbourhood around every point
  have hmem : ∀ t : S, p.base ⁻¹' {t} ⊆ Set.range (eqLocusι f g hf hg).base := fun t => by
    have ht : t ∈ U₁ := by rw [huniv]; trivial
    exact ht
  have hall : ∀ t : S, ∃ U₀ : S.Opens, t ∈ U₀ ∧
      ∃ w : ((p ⁻¹ᵁ U₀) : X.Opens).toScheme ⟶ eqLocus f g hf hg,
        w ≫ eqLocusι f g hf hg = ((p ⁻¹ᵁ U₀) : X.Opens).ι :=
    fun t => exists_open_factor_of_fibre_subset hp e he f g hf hg hgconst t (hmem t)
  choose U₀ hU₀mem w₀ hw₀ using hall
  -- the preimages cover `X`
  have hcover : TopologicalSpace.IsOpenCover fun t : S => (p ⁻¹ᵁ U₀ t : X.Opens) := by
    refine eq_top_iff.mpr fun x _ => ?_
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨p.base x, hU₀mem (p.base x)⟩
  set 𝒰 := X.openCoverOfIsOpenCover _ hcover with h𝒰
  have hface : ∀ t, 𝒰.f t = ((p ⁻¹ᵁ U₀ t : X.Opens)).ι := fun t => rfl
  have hcompat : ∀ a b, pullback.fst (𝒰.f a) (𝒰.f b) ≫ w₀ a =
      pullback.snd (𝒰.f a) (𝒰.f b) ≫ w₀ b := by
    intro a b
    rw [← cancel_mono (eqLocusι f g hf hg)]
    have e1 : (pullback.fst (𝒰.f a) (𝒰.f b) ≫ w₀ a) ≫ eqLocusι f g hf hg =
        pullback.fst (𝒰.f a) (𝒰.f b) ≫ ((p ⁻¹ᵁ U₀ a : X.Opens)).ι :=
      (Category.assoc _ _ _).trans
        (congrArg (pullback.fst (𝒰.f a) (𝒰.f b) ≫ ·) (hw₀ a))
    have e2 : (pullback.snd (𝒰.f a) (𝒰.f b) ≫ w₀ b) ≫ eqLocusι f g hf hg =
        pullback.snd (𝒰.f a) (𝒰.f b) ≫ ((p ⁻¹ᵁ U₀ b : X.Opens)).ι :=
      (Category.assoc _ _ _).trans
        (congrArg (pullback.snd (𝒰.f a) (𝒰.f b) ≫ ·) (hw₀ b))
    have e3 : pullback.fst (𝒰.f a) (𝒰.f b) ≫ ((p ⁻¹ᵁ U₀ a : X.Opens)).ι =
        pullback.snd (𝒰.f a) (𝒰.f b) ≫ ((p ⁻¹ᵁ U₀ b : X.Opens)).ι := by
      rw [← hface a, ← hface b]
      exact pullback.condition
    exact e1.trans (e3.trans e2.symm)
  refine ⟨𝒰.glueMorphisms w₀ hcompat, 𝒰.hom_ext _ _ fun t => ?_⟩
  have hend : 𝒰.f t ≫ 𝟙 X = ((p ⁻¹ᵁ U₀ t : X.Opens)).ι := by
    rw [Category.comp_id]
    exact hface t
  rw [hend]
  calc 𝒰.f t ≫ 𝒰.glueMorphisms w₀ hcompat ≫ eqLocusι f g hf hg
      = (𝒰.f t ≫ 𝒰.glueMorphisms w₀ hcompat) ≫ eqLocusι f g hf hg :=
        (Category.assoc _ _ _).symm
    _ = w₀ t ≫ eqLocusι f g hf hg :=
        congrArg (· ≫ eqLocusι f g hf hg) (𝒰.ι_glueMorphisms w₀ hcompat t)
    _ = ((p ⁻¹ᵁ U₀ t : X.Opens)).ι := hw₀ t

/-- **(T-W7.r2·d, connected-base wrapper)** On a connected base one seed fibre suffices:
its component is everything. -/
theorem exists_factor_of_connected [IsLocallyNoetherian S] [IsProper p] [Flat p]
    (hconn : ConnectedSpace S)
    (hp : UniversallyOConnected p) (e : S ⟶ X) (he : e ≫ p = 𝟙 S)
    (f g : X ⟶ Y) (hf : f ≫ q = p) (hg : g ≫ q = p)
    (hgconst : g = p ≫ (e ≫ f)) (s : S)
    (hseed : p.base ⁻¹' {s} ⊆ Set.range (eqLocusι f g hf hg).base) :
    ∃ w : X ⟶ eqLocus f g hf hg, w ≫ eqLocusι f g hf hg = 𝟙 X := by
  refine exists_factor_of_forall_component hp e he f g hf hg hgconst (fun t => ⟨s, ?_, hseed⟩)
  haveI := hconn
  rw [PreconnectedSpace.connectedComponent_eq_univ t]
  trivial

end RigidityLeaves

/-- **(T-W7.7a, GIT Prop 6.1, case 2)** The rigidity lemma: `S` connected and locally
noetherian, `p : X ⟶ S` proper flat and universally `O`-connected with a section, `Y ⟶ S`
separated, `f : X ⟶ Y` an `S`-morphism collapsing ONE fibre `X_s` to a single point. Then
`f` factors through a section of `Y ⟶ S`. Mechanism (the globalization over nilpotents that
density arguments cannot deliver): case 1 over every Artinian subscheme concentrated at `t`
upgrades set-theoretic fibre containment in the equalizer `Z = (f, η∘p)⁻¹(Δ)` to
scheme-theoretic containment of `p⁻¹(T)`; Krull intersection + coherence give an open
neighbourhood; flatness (open image) + closedness of `Z` make the good locus clopen;
connectedness finishes. Source: GIT pp. 115–116, transcribed verbatim (quotes file). -/
theorem rigidity {X Y S : Scheme.{u}} [IsLocallyNoetherian S]
    (hconn : ConnectedSpace S)
    {p : X ⟶ S} [IsProper p] [Flat p] (hp : UniversallyOConnected p)
    (e : S ⟶ X) (he : e ≫ p = 𝟙 S)
    {q : Y ⟶ S} [IsSeparated q] (f : X ⟶ Y) (hf : f ≫ q = p)
    (s : S) (hs : Set.Subsingleton (f.base '' (p.base ⁻¹' {s}))) :
    ∃ sec : S ⟶ Y, sec ≫ q = 𝟙 S ∧ f = p ≫ sec := by
  -- Assembled from the three leaves above (T-W7.r2·b/c/d); leaf ·c is consumed by ·d.
  refine ⟨e ≫ f, by rw [Category.assoc, hf, he], ?_⟩
  have hg : (p ≫ (e ≫ f)) ≫ q = p := by
    rw [Category.assoc, Category.assoc, hf, he]
    exact Category.comp_id p
  obtain ⟨w, hw⟩ := exists_factor_of_connected hconn hp e he f (p ≫ (e ≫ f)) hf hg rfl s
    (fibre_subset_eqLocus_of_collapsed hp e he f hf s hs)
  calc f = (w ≫ eqLocusι f (p ≫ (e ≫ f)) hf hg) ≫ f := by rw [hw, Category.id_comp]
    _ = w ≫ (eqLocusι f (p ≫ (e ≫ f)) hf hg ≫ f) := Category.assoc _ _ _
    _ = w ≫ (eqLocusι f (p ≫ (e ≫ f)) hf hg ≫ (p ≫ (e ≫ f))) :=
        congrArg (w ≫ ·) (eqLocusι_comp_eq f (p ≫ (e ≫ f)) hf hg)
    _ = (w ≫ eqLocusι f (p ≫ (e ≫ f)) hf hg) ≫ (p ≫ (e ≫ f)) := (Category.assoc _ _ _).symm
    _ = p ≫ (e ≫ f) := by rw [hw, Category.id_comp]

/-- **(T-W7.7a′, rigidity with a seed in every component)** The disconnected-base form of
GIT Prop 6.1: if EVERY connected component of `S` contains a point whose fibre `f`
collapses, then `f` factors through a section — the clopen good locus meets every
component, so it is everything; no connectedness needed. Engine for the componentwise
canonicity glue (C4glue). -/
theorem rigidity_of_forall_component {X Y S : Scheme.{u}} [IsLocallyNoetherian S]
    {p : X ⟶ S} [IsProper p] [Flat p] (hp : UniversallyOConnected p)
    (e : S ⟶ X) (he : e ≫ p = 𝟙 S)
    {q : Y ⟶ S} [IsSeparated q] (f : X ⟶ Y) (hf : f ≫ q = p)
    (hs : ∀ t : S, ∃ s ∈ connectedComponent t,
      Set.Subsingleton (f.base '' (p.base ⁻¹' {s}))) :
    ∃ sec : S ⟶ Y, sec ≫ q = 𝟙 S ∧ f = p ≫ sec := by
  refine ⟨e ≫ f, by rw [Category.assoc, hf, he], ?_⟩
  have hg : (p ≫ (e ≫ f)) ≫ q = p := by
    rw [Category.assoc, Category.assoc, hf, he]
    exact Category.comp_id p
  obtain ⟨w, hw⟩ := exists_factor_of_forall_component hp e he f (p ≫ (e ≫ f)) hf hg rfl
    (fun t => by
      obtain ⟨s, hscomp, hssub⟩ := hs t
      exact ⟨s, hscomp, fibre_subset_eqLocus_of_collapsed hp e he f hf s hssub⟩)
  calc f = (w ≫ eqLocusι f (p ≫ (e ≫ f)) hf hg) ≫ f := by rw [hw, Category.id_comp]
    _ = w ≫ (eqLocusι f (p ≫ (e ≫ f)) hf hg ≫ f) := Category.assoc _ _ _
    _ = w ≫ (eqLocusι f (p ≫ (e ≫ f)) hf hg ≫ (p ≫ (e ≫ f))) :=
        congrArg (w ≫ ·) (eqLocusι_comp_eq f (p ≫ (e ≫ f)) hf hg)
    _ = (w ≫ eqLocusι f (p ≫ (e ≫ f)) hf hg) ≫ (p ≫ (e ≫ f)) := (Category.assoc _ _ _).symm
    _ = p ≫ (e ≫ f) := by rw [hw, Category.id_comp]

/-! ### The corollary chain, split (coordinator §2): C1 (Cor 6.2) → C2 (Cor 6.3) → C3 -/

/-- **(T-W7.7·C2conn·idem — clopen-to-idempotent leaf)** A scheme whose ring of global
sections is a field is preconnected: a nontrivial clopen decomposition glues the section
`(1, 0)`, giving a global idempotent that a field forces to `0` or `1`; either case kills
one nonempty piece via the nontriviality of a stalk. No mathlib name (2026-07-07); upstream
candidate. -/
theorem preconnectedSpace_of_isField {Z : Scheme.{u}} (hf : IsField ↑(Γ(Z, ⊤))) :
    PreconnectedSpace Z := by
  rw [preconnectedSpace_iff_clopen]
  intro s hs
  rw [or_iff_not_imp_left]
  intro hs0
  by_contra hsu
  have hs1 : s.Nonempty := Set.nonempty_iff_ne_empty.mpr hs0
  have hs2 : sᶜ.Nonempty := Set.nonempty_compl.mpr hsu
  classical
  set U : Bool → Z.Opens :=
    fun b => if b then ⟨s, hs.isOpen⟩ else ⟨sᶜ, hs.isClosed.isOpen_compl⟩ with hU
  have hmem₁ : ∀ z ∈ s, z ∈ U true := fun z hz => by simpa [hU] using hz
  have hmem₂ : ∀ z ∈ sᶜ, z ∈ U false := fun z hz => by simpa [hU] using hz
  have hdisj : U true ⊓ U false = ⊥ := by
    apply TopologicalSpace.Opens.ext
    simp [hU]
  have hcover : (⊤ : Z.Opens) ≤ iSup U := by
    intro z _
    rw [TopologicalSpace.Opens.mem_iSup]
    by_cases hz : z ∈ s
    · exact ⟨true, hmem₁ z hz⟩
    · exact ⟨false, hmem₂ z hz⟩
  have hsub : Subsingleton (ToType (Γ(Z, U true ⊓ U false))) := by
    rw [hdisj]; infer_instance
  have hsub' : Subsingleton (ToType (Γ(Z, U false ⊓ U true))) := by
    rw [inf_comm, hdisj]; infer_instance
  -- glue the idempotent candidate: `1` on `s`, `0` on `sᶜ`
  have hglue : ∃ χ : ↑(Γ(Z, ⊤)),
      (Z.presheaf.map (homOfLE (le_top : U true ≤ ⊤)).op).hom χ = 1 ∧
      (Z.presheaf.map (homOfLE (le_top : U false ≤ ⊤)).op).hom χ = 0 := by
    obtain ⟨χ, hχ, -⟩ := Z.sheaf.existsUnique_gluing' U ⊤ (fun _ => homOfLE le_top) hcover
      (fun b => match b with
        | true => (1 : ToType (Γ(Z, U true)))
        | false => (0 : ToType (Γ(Z, U false))))
      (by
        intro i j
        match i, j with
        | true, true => rfl
        | false, false => rfl
        | true, false => exact hsub.elim _ _
        | false, true => exact hsub'.elim _ _)
    exact ⟨χ, hχ true, hχ false⟩
  obtain ⟨χ, h₁, h₂⟩ := hglue
  have hcover₂ : (⊤ : Z.Opens) ≤ U true ⊔ U false := by
    intro z _
    rw [TopologicalSpace.Opens.mem_sup]
    by_cases hz : z ∈ s
    · exact Or.inl (hmem₁ z hz)
    · exact Or.inr (hmem₂ z hz)
  have hidem : χ * (χ - 1) = 0 := by
    apply Z.sheaf.eq_of_locally_eq₂ (homOfLE (le_top : U true ≤ ⊤))
      (homOfLE (le_top : U false ≤ ⊤)) hcover₂
    · show (Z.presheaf.map (homOfLE (le_top : U true ≤ ⊤)).op).hom (χ * (χ - 1)) =
        (Z.presheaf.map (homOfLE (le_top : U true ≤ ⊤)).op).hom 0
      rw [map_mul, map_sub, map_one, map_zero, h₁]
      ring
    · show (Z.presheaf.map (homOfLE (le_top : U false ≤ ⊤)).op).hom (χ * (χ - 1)) =
        (Z.presheaf.map (homOfLE (le_top : U false ≤ ⊤)).op).hom 0
      rw [map_mul, map_sub, map_one, map_zero, h₂]
      ring
  rcases eq_or_ne χ 0 with h0 | hne
  · -- `χ = 0` makes `1 = 0` on the nonempty open `s`
    obtain ⟨z, hz⟩ := hs1
    have hz' : z ∈ U true := hmem₁ z hz
    have hbad : (1 : ToType (Γ(Z, U true))) = 0 := by
      rw [← h₁, h0, map_zero]
    exact one_ne_zero (α := ToType (Z.presheaf.stalk z))
      (by simpa using congrArg (Z.presheaf.germ (U true) z hz').hom hbad)
  · -- otherwise the field inverts `χ`, so `χ = 1` makes `1 = 0` on the nonempty `sᶜ`
    obtain ⟨inv, hinv⟩ := hf.mul_inv_cancel hne
    have hχ1 : χ = 1 := by
      have h1' : χ - 1 = 0 := by
        calc χ - 1 = (χ * inv) * (χ - 1) := by rw [hinv]; ring
          _ = inv * (χ * (χ - 1)) := by ring
          _ = inv * 0 := by rw [hidem]
          _ = 0 := mul_zero inv
      exact sub_eq_zero.mp h1'
    obtain ⟨z, hz⟩ := hs2
    have hz' : z ∈ U false := hmem₂ z hz
    have hbad : (1 : ToType (Γ(Z, U false))) = 0 := by
      rw [← h₂, hχ1, map_one]
    exact one_ne_zero (α := ToType (Z.presheaf.stalk z))
      (by simpa using congrArg (Z.presheaf.germ (U false) z hz').hom hbad)

/-- **(T-W7.7·C2conn·fib)** Fibres of a universally-`O`-connected family with a section
are connected: `Γ(fibre) ≅ κ(t)` is a field, so the fibre is preconnected
(`preconnectedSpace_of_isField`), and the section provides a point. -/
theorem isConnected_fibre_of_universallyOConnected {X S : Scheme.{u}} {p : X ⟶ S}
    (hp : UniversallyOConnected p) (e : S ⟶ X) (he : e ≫ p = 𝟙 S) (t : S) :
    _root_.IsConnected (p.base ⁻¹' {t}) := by
  -- the fibre is the range of the projection from the residue-field pullback
  have hrange : Set.range (pullback.fst p (S.fromSpecResidueField t)).base
      = p.base ⁻¹' {t} := by
    rw [Scheme.Pullback.range_fst p (S.fromSpecResidueField t),
      Scheme.range_fromSpecResidueField]
  -- nonempty, via the section
  have hne : (p.base ⁻¹' {t}).Nonempty := by
    refine ⟨e.base t, ?_⟩
    have hpe := congrArg (fun m : S ⟶ S => m.base t) he
    simpa using hpe
  haveI : Nonempty ↥(pullback p (S.fromSpecResidueField t)) := by
    rw [← hrange] at hne
    exact Set.range_nonempty_iff_nonempty.mp hne
  -- global sections of the fibre form the field `κ(t)`, by `O`-connectedness
  have hfield : IsField ↑(Γ(pullback p (S.fromSpecResidueField t), ⊤)) := by
    haveI hiso : IsIso ((pullback.snd p (S.fromSpecResidueField t)).app ⊤) :=
      hp (S.fromSpecResidueField t) ⊤
    have e₂ :=
      (asIso ((pullback.snd p (S.fromSpecResidueField t)).app ⊤)).commRingCatIsoToRingEquiv
    have e₁ := (Scheme.ΓSpecIso (S.residueField t)).commRingCatIsoToRingEquiv
    exact (e₂.symm.trans e₁).toMulEquiv.isField (Field.toIsField ↑(S.residueField t))
  haveI : PreconnectedSpace ↥(pullback p (S.fromSpecResidueField t)) :=
    preconnectedSpace_of_isField hfield
  haveI : ConnectedSpace ↥(pullback p (S.fromSpecResidueField t)) := ⟨‹_›⟩
  rw [← hrange]
  exact isConnected_range (pullback.fst p (S.fromSpecResidueField t)).base.hom.continuous

/-- **(T-W7.7·C2conn, PROVEN)** The total space of a proper flat universally-`O`-connected
family with a section over a connected locally noetherian base is connected — GIT Cor 6.3
runs its connectedness argument along the SECOND factor, so C3's application to `A ⊗ A`
needs `A.left` connected, not just `S`. Assembly: `p` is open (flat + lfp over locally
noetherian, as in T-W7.r2·d) and closed (proper); each fibre is the range of
`pullback.fst p (S.fromSpecResidueField t)`, whose total space has global sections the
field `κ(t)` by `O`-connectedness, hence is preconnected (`preconnectedSpace_of_isField`)
and nonempty (the section); `connectedSpace_of_isOpenMap_of_isClosedMap_of_isConnected_-
preimage` closes. `[IsLocallyNoetherian S]` was added to the original skeleton statement
for the open-map instance chain — every consumer (C1–C4) already assumes it. -/
theorem connectedSpace_of_universallyOConnected {X S : Scheme.{u}} {p : X ⟶ S}
    [IsLocallyNoetherian S] [IsProper p] [Flat p]
    (hp : UniversallyOConnected p) (e : S ⟶ X) (he : e ≫ p = 𝟙 S)
    [hconn : ConnectedSpace S] : ConnectedSpace X :=
  connectedSpace_of_isOpenMap_of_isClosedMap_of_isConnected_preimage
    p.isOpenMap p.isClosedMap
    (fun t => isConnected_fibre_of_universallyOConnected hp e he t)

/-- Components of the GIT pointwise-quotient collapse: if `h` equalizes `f` and `g` into a
group object, then `h ≫ (f · g⁻¹)` is the unit constant, in `Over`-components. Generic
supply for C1/C2. -/
lemma comp_mul_inv_left {S : Scheme.{u}} {P A G : Over S} [GrpObj G]
    (h : P ⟶ A) (f g : A ⟶ G) (hfg : h ≫ f = h ≫ g) :
    h.left ≫ (f * g⁻¹).left = P.hom ≫ η[G].left := by
  have h1 : h ≫ (f * g⁻¹) = (1 : P ⟶ G) := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, hfg, _root_.mul_inv_cancel]
  have h2 := congrArg CommaMorphism.left h1
  simpa [Over.comp_left, Hom.one_def, Over.toUnit_left] using h2

/-- Mirror of `comp_mul_inv_left` for the left quotient `f⁻¹ · g`: the order matters for the
GIT 6.4 endgame (Mumford's `g(x)·h(y)` with the `x`-factor on the LEFT is what makes the
pointed map a homomorphism rather than an antihomomorphism). -/
lemma comp_inv_mul_left {S : Scheme.{u}} {P A G : Over S} [GrpObj G]
    (h : P ⟶ A) (f g : A ⟶ G) (hfg : h ≫ f = h ≫ g) :
    h.left ≫ (f⁻¹ * g).left = P.hom ≫ η[G].left := by
  have h1 : h ≫ (f⁻¹ * g) = (1 : P ⟶ G) := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, hfg, inv_mul_cancel]
  have h2 := congrArg CommaMorphism.left h1
  simpa [Over.comp_left, Hom.one_def, Over.toUnit_left] using h2

/-- **(T-W7.7·C1, GIT Cor 6.2, PROVEN)** Two `S`-morphisms from a proper flat
universally-`O`-connected pointed `A` into a separated group object `G` that agree on ONE
fibre differ by a constant section: `f = (χ ∘ toUnit) · g` for a point `χ` of `G`. Proof:
`rigidity` applied to the pointwise quotient `f · g⁻¹` (the `Hom`-group of `G`), whose
`s`-fibre image is the single point `η(s)` by the fibre-equality hypothesis. The point
`e` of `A` supplies rigidity's section — faithful to the banked case-2 scope decision
(quotes file: case 3 = sectionless fppf descent is NOT NEEDED for T-W7, `E` has the zero
section); logged per rule 5. Source: GIT p. 116, Cor 6.2 (verbatim in quotes file). -/
theorem eq_mul_of_fibre_eq {S : Scheme.{u}} [IsLocallyNoetherian S]
    (hconn : ConnectedSpace S) {A G : Over S} [GrpObj G]
    [IsProper A.hom] [Flat A.hom] (hO : UniversallyOConnected A.hom)
    [IsSeparated G.hom] (e : 𝟙_ (Over S) ⟶ A) (f g : A ⟶ G) (s : S)
    (hfib : pullback.fst A.hom (S.fromSpecResidueField s) ≫ f.left =
      pullback.fst A.hom (S.fromSpecResidueField s) ≫ g.left) :
    ∃ χ : 𝟙_ (Over S) ⟶ G, f = lift (toUnit A ≫ χ) g ≫ μ[G] := by
  -- the projection from the fibre, as a morphism over `S`
  have hfib' : (Over.homMk (pullback.fst A.hom (S.fromSpecResidueField s)) rfl :
      Over.mk (pullback.fst A.hom (S.fromSpecResidueField s) ≫ A.hom) ⟶ A) ≫ f =
      (Over.homMk (pullback.fst A.hom (S.fromSpecResidueField s)) rfl) ≫ g :=
    Over.OverMorphism.ext (by simp only [Over.comp_left, Over.homMk_left]; exact hfib)
  -- the quotient `f · g⁻¹` collapses the `s`-fibre to the unit's image point
  have hconst0 := comp_mul_inv_left _ f g hfib'
  simp only [Over.homMk_left, Over.mk_hom] at hconst0
  -- re-type the components equation at the pullback (defeq, but syntactically clean)
  have hconst : pullback.fst A.hom (S.fromSpecResidueField s) ≫ (f * g⁻¹).left
      = (pullback.fst A.hom (S.fromSpecResidueField s) ≫ A.hom) ≫ η[G].left := hconst0
  have hsub : Set.Subsingleton ((f * g⁻¹).left.base '' (A.hom.base ⁻¹' {s})) := by
    have hrange : A.hom.base ⁻¹' {s}
        = Set.range (pullback.fst A.hom (S.fromSpecResidueField s)).base := by
      rw [Scheme.Pullback.range_fst A.hom (S.fromSpecResidueField s),
        Scheme.range_fromSpecResidueField]
    have hval : ∀ w : ↥(pullback A.hom (S.fromSpecResidueField s)),
        (f * g⁻¹).left ((pullback.fst A.hom (S.fromSpecResidueField s)) w)
          = η[G].left s := by
      intro w
      have hbase := congrArg (fun m : (pullback A.hom (S.fromSpecResidueField s) :
          Scheme.{u}) ⟶ G.left => m w) hconst
      have hs' : (pullback.fst A.hom (S.fromSpecResidueField s) ≫ A.hom) w = s := by
        rw [pullback.condition]
        have hmem : (pullback.snd A.hom (S.fromSpecResidueField s) ≫
            S.fromSpecResidueField s) w ∈ Set.range (S.fromSpecResidueField s).base := by
          rw [Scheme.Hom.comp_apply]
          exact Set.mem_range_self _
        rwa [Scheme.range_fromSpecResidueField] at hmem
      simp only [Scheme.Hom.comp_apply] at hbase hs'
      rw [hs'] at hbase
      exact hbase
    rw [hrange, ← Set.range_comp]
    rintro y ⟨w, rfl⟩ y' ⟨w', rfl⟩
    simp only [Function.comp_apply]
    rw [hval w, hval w']
  -- rigidity factors the quotient through a section of `G`
  obtain ⟨sec, hsecq, hfac⟩ :=
    rigidity hconn hO e.left (Over.w e) (f * g⁻¹).left (Over.w (f * g⁻¹)) s hsub
  refine ⟨Over.homMk sec hsecq, ?_⟩
  have hφconst : f * g⁻¹ = toUnit A ≫ Over.homMk sec hsecq :=
    Over.OverMorphism.ext (by simpa [Over.comp_left, Over.toUnit_left] using hfac)
  calc f = (f * g⁻¹) * g := (inv_mul_cancel_right f g).symm
    _ = (toUnit A ≫ Over.homMk sec hsecq) * g := by rw [hφconst]
    _ = lift (toUnit A ≫ Over.homMk sec hsecq) g ≫ μ[G] := Hom.mul_def _ _

/-- **(T-W7.7·C2·res — residue-field retraction rigidity)** Along a section–retraction pair
`e ≫ q = 𝟙 S`, the canonical map from the residue field of a point in the section's image
absorbs the roundtrip `q ≫ e`: the two residue maps are a split pair of field maps, hence
both isomorphisms with composite the congr iso. Supply for C2·fib. -/
lemma fromSpecResidueField_comp_section {B S : Scheme.{u}} (q : B ⟶ S) (e : S ⟶ B)
    (he : e ≫ q = 𝟙 S) (s : S) :
    B.fromSpecResidueField (e.base s) ≫ q ≫ e = B.fromSpecResidueField (e.base s) := by
  have hqe : q.base (e.base s) = s := by
    have h := congrArg (fun m : S ⟶ S => m.base s) he
    simpa using h
  have hcomp : q.residueFieldMap (e.base s) ≫ e.residueFieldMap s
      = (S.residueFieldCongr hqe).hom := by
    have h1 := Scheme.residueFieldMap_comp e q s
    rw [Scheme.Hom.residueFieldMap_congr he s] at h1
    simpa [Scheme.residueFieldMap_id] using h1.symm
  haveI hmono : Mono (e.residueFieldMap s) :=
    ConcreteCategory.mono_of_injective _ (RingHom.injective _)
  haveI hsplit : IsSplitEpi (e.residueFieldMap s) :=
    IsSplitEpi.mk' ⟨(S.residueFieldCongr hqe).inv ≫ q.residueFieldMap (e.base s), by
      rw [Category.assoc, hcomp, Iso.inv_hom_id]⟩
  haveI : IsIso (e.residueFieldMap s) := isIso_of_mono_of_isSplitEpi _
  have hu : q.residueFieldMap (e.base s)
      = (S.residueFieldCongr hqe).hom ≫ inv (e.residueFieldMap s) := by
    rw [← hcomp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  calc B.fromSpecResidueField (e.base s) ≫ q ≫ e
      = (B.fromSpecResidueField (e.base s) ≫ q) ≫ e := (Category.assoc _ _ _).symm
    _ = (Spec.map (q.residueFieldMap (e.base s))
          ≫ S.fromSpecResidueField (q.base (e.base s))) ≫ e := by
        rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    _ = Spec.map (q.residueFieldMap (e.base s))
          ≫ (Spec.map (S.residueFieldCongr hqe).inv ≫ S.fromSpecResidueField s) ≫ e := by
        rw [← Scheme.residueFieldCongr_fromSpecResidueField hqe, ← Spec.map_comp_assoc,
          Iso.hom_inv_id, Spec.map_id, Category.id_comp, Category.assoc]
    _ = Spec.map (q.residueFieldMap (e.base s)) ≫ Spec.map (S.residueFieldCongr hqe).inv
          ≫ Spec.map (e.residueFieldMap s) ≫ B.fromSpecResidueField (e.base s) := by
        rw [Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    _ = Spec.map (e.residueFieldMap s ≫ (S.residueFieldCongr hqe).inv
          ≫ q.residueFieldMap (e.base s)) ≫ B.fromSpecResidueField (e.base s) := by
        rw [Spec.map_comp, Spec.map_comp]
        simp only [Category.assoc]
    _ = B.fromSpecResidueField (e.base s) := by
        rw [hu, Iso.inv_hom_id_assoc, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]

/-- **(T-W7.7·C2, GIT Cor 6.3, PROVEN)** A morphism `A ⊗ B ⟶ G` out of a product, with `A`
proper flat universally-`O`-connected carrying a unit point, `B` pointed with `B.left`
connected locally noetherian, splits as a product `f(x,y) = g(x)·h(y)`. Proof (raw-scheme
route, all Hom-group algebra in `Over S`): `δ := (Ẽ ≫ f)⁻¹ · f` for the second-argument
freeze `Ẽ := lift (fst) (toUnit ≫ e₂)`; rigidity over the base `B.left` applied to
`⟨δ.left, snd⟩` into `pullback G.hom B.hom` (instances by base change), with section
`(B.hom ≫ e₁.left, 𝟙)` and collapsed fibre over `y₀ := e₂(B.hom b₀)` — the fibre inclusion
fixes `Ẽ` by the residue-retraction lemma, so `δ` is unit-constant there
(`comp_mul_inv_left`), and the fibre image lands in the one-point `Spec κ(y₀)`-factor.
Statement changes logged on the board (rule 5): `e₂` (the source quote's second point) and
`[IsLocallyNoetherian B.left]`; the product order is Mumford's `g(x)·h(y)` — obtained from
the LEFT quotient `(Ẽ≫f)⁻¹·f`, and load-bearing: the flipped order would make GIT 6.4
produce an antihomomorphism. Source: GIT p. 116, Cor 6.3 (verbatim in quotes file). -/
theorem factor_mul_of_tensor_of_forall_component {S : Scheme.{u}} [IsLocallyNoetherian S]
    {A B G : Over S} [GrpObj G] [IsLocallyNoetherian B.left]
    [IsProper A.hom] [Flat A.hom] (hO : UniversallyOConnected A.hom)
    (e₁ : 𝟙_ (Over S) ⟶ A) (e₂ : 𝟙_ (Over S) ⟶ B)
    (hfix : ∀ t : ↥B.left, ∃ b ∈ connectedComponent t, e₂.left.base (B.hom.base b) = b)
    [IsSeparated G.hom] (f : A ⊗ B ⟶ G) :
    ∃ (g : A ⟶ G) (h : B ⟶ G),
      f = lift (fst A B ≫ g) (snd A B ≫ h) ≫ μ[G] := by
  classical
  -- freeze the second argument at the point `e₂` (all Hom-group algebra stays in `Over S`)
  set E : A ⊗ B ⟶ A ⊗ B := lift (fst A B) (toUnit (A ⊗ B) ≫ e₂) with hE
  -- raw-typed bridges across the `tensorObj_left`/`tensorUnit_left` defeq seams
  set El : pullback A.hom B.hom ⟶ pullback A.hom B.hom := E.left with hEl
  set fl : pullback A.hom B.hom ⟶ G.left := f.left with hfl
  set δl : pullback A.hom B.hom ⟶ G.left := ((E ≫ f)⁻¹ * f).left with hδl
  set ηl : S ⟶ G.left := η[G].left with hηl
  set e₂l : S ⟶ B.left := e₂.left with he₂l
  have he₂B : e₂l ≫ B.hom = 𝟙 S := Over.w e₂
  -- the difference, over the base `B.left`, into the base-changed group
  have hδq : δl ≫ G.hom = pullback.snd A.hom B.hom ≫ B.hom := by
    have hw : δl ≫ G.hom = pullback.fst A.hom B.hom ≫ A.hom := Over.w ((E ≫ f)⁻¹ * f)
    rw [hw, pullback.condition]
  -- components of the frozen map, in the raw spelling
  have hElfst : El ≫ pullback.fst A.hom B.hom = pullback.fst A.hom B.hom := by
    have h := congrArg CommaMorphism.left (lift_fst (fst A B) (toUnit (A ⊗ B) ≫ e₂))
    simp only [Over.comp_left, Over.fst_left] at h
    rw [hEl, hE]
    exact h
  have hElsnd : El ≫ pullback.snd A.hom B.hom
      = pullback.snd A.hom B.hom ≫ B.hom ≫ e₂l := by
    have h := congrArg CommaMorphism.left (lift_snd (fst A B) (toUnit (A ⊗ B) ≫ e₂))
    simp only [Over.comp_left, Over.snd_left, Over.toUnit_left, Over.tensorObj_hom] at h
    have h2 : (pullback.fst A.hom B.hom ≫ A.hom) ≫ e₂l
        = pullback.snd A.hom B.hom ≫ B.hom ≫ e₂l := by
      rw [pullback.condition (f := A.hom) (g := B.hom)]
      simp only [Category.assoc]
    rw [hEl, hE]
    exact h.trans h2
  -- the collapse locus: every fixed point of `e₂ ∘ q` has subsingleton fibre image
  have key : ∀ y₀ : ↥B.left, e₂l.base (B.hom.base y₀) = y₀ →
      Set.Subsingleton ((pullback.lift δl (pullback.snd A.hom B.hom) hδq).base ''
        ((pullback.snd A.hom B.hom).base ⁻¹' {y₀})) := by
    intro y₀ hbfix
    -- the fibre inclusion over `y₀` fixes the frozen map (C2·fib, via C2·res)
    have hEfix : pullback.fst (pullback.snd A.hom B.hom) (B.left.fromSpecResidueField y₀)
        ≫ El = pullback.fst (pullback.snd A.hom B.hom) (B.left.fromSpecResidueField y₀) := by
      apply pullback.hom_ext
      · rw [Category.assoc, hElfst]
      · rw [Category.assoc, hElsnd,
          ← Category.assoc, pullback.condition (f := pullback.snd A.hom B.hom)
            (g := B.left.fromSpecResidueField y₀)]
        simp only [Category.assoc]
        have hres := fromSpecResidueField_comp_section B.hom e₂l he₂B (B.hom.base y₀)
        rw [hbfix] at hres
        rw [hres]
    -- morphism-level fibre agreement of `f` and `E ≫ f`, packaged over `S`
    have hgoalIf : pullback.fst (pullback.snd A.hom B.hom) (B.left.fromSpecResidueField y₀)
        ≫ fl = pullback.fst (pullback.snd A.hom B.hom) (B.left.fromSpecResidueField y₀)
          ≫ El ≫ fl := by
      rw [← Category.assoc, hEfix]
    have hIf : (Over.homMk (pullback.fst (pullback.snd A.hom B.hom)
          (B.left.fromSpecResidueField y₀)) rfl :
        Over.mk (pullback.fst (pullback.snd A.hom B.hom) (B.left.fromSpecResidueField y₀)
          ≫ (A ⊗ B).hom) ⟶ A ⊗ B) ≫ f
        = (Over.homMk (pullback.fst (pullback.snd A.hom B.hom)
            (B.left.fromSpecResidueField y₀)) rfl) ≫ (E ≫ f) := by
      apply Over.OverMorphism.ext
      simp only [Over.comp_left, Over.homMk_left]
      exact hgoalIf
    have hconst0 := comp_inv_mul_left _ (E ≫ f) f hIf.symm
    simp only [Over.homMk_left, Over.mk_hom] at hconst0
    have hconst : pullback.fst (pullback.snd A.hom B.hom) (B.left.fromSpecResidueField y₀)
        ≫ δl
        = (pullback.fst (pullback.snd A.hom B.hom) (B.left.fromSpecResidueField y₀)
            ≫ (pullback.fst A.hom B.hom ≫ A.hom)) ≫ ηl := hconst0
    -- the restricted difference factors through the one-point `Spec κ(y₀)`
    have hη : ηl ≫ G.hom = 𝟙 S := Over.w η[G]
    have hzw : (B.left.fromSpecResidueField y₀ ≫ B.hom ≫ ηl) ≫ G.hom
        = B.left.fromSpecResidueField y₀ ≫ B.hom := by
      rw [Category.assoc, Category.assoc, hη, Category.comp_id]
    have hfactor : pullback.fst (pullback.snd A.hom B.hom) (B.left.fromSpecResidueField y₀)
          ≫ pullback.lift δl (pullback.snd A.hom B.hom) hδq
        = pullback.snd (pullback.snd A.hom B.hom) (B.left.fromSpecResidueField y₀)
          ≫ pullback.lift (B.left.fromSpecResidueField y₀ ≫ B.hom ≫ ηl)
              (B.left.fromSpecResidueField y₀) hzw := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst, hconst]
        simp only [← Category.assoc]
        congr 1
        rw [← pullback.condition (f := pullback.snd A.hom B.hom)
          (g := B.left.fromSpecResidueField y₀)]
        simp only [Category.assoc]
        rw [pullback.condition (f := A.hom) (g := B.hom)]
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd]
        exact pullback.condition
    have hsub : Set.Subsingleton
        ((pullback.lift δl (pullback.snd A.hom B.hom) hδq).base ''
          ((pullback.snd A.hom B.hom).base ⁻¹' {y₀})) := by
      have hrange : (pullback.snd A.hom B.hom).base ⁻¹' {y₀}
          = Set.range (pullback.fst (pullback.snd A.hom B.hom)
              (B.left.fromSpecResidueField y₀)).base := by
        rw [Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]
      rw [hrange, ← Set.range_comp]
      rintro p ⟨w, rfl⟩ p' ⟨w', rfl⟩
      have h1 : ∀ v, ((pullback.lift δl (pullback.snd A.hom B.hom) hδq).base
            ∘ (pullback.fst (pullback.snd A.hom B.hom)
                (B.left.fromSpecResidueField y₀)).base) v
          = (pullback.lift (B.left.fromSpecResidueField y₀ ≫ B.hom ≫ ηl)
                (B.left.fromSpecResidueField y₀) hzw).base
              ((pullback.snd (pullback.snd A.hom B.hom)
                (B.left.fromSpecResidueField y₀)).base v) := by
        intro v
        have h2 := congrArg (fun m : (pullback (pullback.snd A.hom B.hom)
            (B.left.fromSpecResidueField y₀) : Scheme.{u}) ⟶ pullback G.hom B.hom => m v)
          hfactor
        simpa [Scheme.Hom.comp_apply] using h2
      rw [h1 w, h1 w']
      exact congrArg _ (Subsingleton.elim _ _)
    exact hsub
  -- rigidity over `B.left`
  haveI hpO : UniversallyOConnected (pullback.snd A.hom B.hom) := hO.baseChange B.hom
  set e₁l : S ⟶ A.left := e₁.left with he₁l
  have he₁A : e₁l ≫ A.hom = 𝟙 S := Over.w e₁
  obtain ⟨sec, hsecq, hfac⟩ := rigidity_of_forall_component hpO
    (pullback.lift (B.hom ≫ e₁l) (𝟙 B.left)
      (by rw [Category.assoc, he₁A, Category.comp_id, Category.id_comp]))
    (pullback.lift_snd _ _ _)
    (pullback.lift δl (pullback.snd A.hom B.hom) hδq)
    (pullback.lift_snd _ _ _)
    (fun t => by
      obtain ⟨b, hbcomp, hbfix⟩ := hfix t
      exact ⟨b, hbcomp, key b hbfix⟩)
  -- extract `h` and close with Hom-group algebra
  have hsecw : (sec ≫ pullback.fst G.hom B.hom) ≫ G.hom = B.hom := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hsecq, Category.id_comp]
  refine ⟨lift (𝟙 A) (toUnit A ≫ e₂) ≫ f,
    Over.homMk (sec ≫ pullback.fst G.hom B.hom) hsecw, ?_⟩
  have h4 : δl = pullback.snd A.hom B.hom ≫ sec ≫ pullback.fst G.hom B.hom := by
    have h3 := congrArg (fun m => m ≫ pullback.fst G.hom B.hom) hfac
    simpa [pullback.lift_fst, Category.assoc] using h3
  have hδsnd : (E ≫ f)⁻¹ * f
      = snd A B ≫ Over.homMk (sec ≫ pullback.fst G.hom B.hom) hsecw := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.homMk_left, Over.snd_left]
    exact h4
  have hEg : E ≫ f = fst A B ≫ (lift (𝟙 A) (toUnit A ≫ e₂) ≫ f) := by
    rw [hE, ← Category.assoc, comp_lift, Category.comp_id, ← Category.assoc, comp_toUnit]
  calc f = (E ≫ f) * ((E ≫ f)⁻¹ * f) := (mul_inv_cancel_left (E ≫ f) f).symm
    _ = (fst A B ≫ (lift (𝟙 A) (toUnit A ≫ e₂) ≫ f))
          * (snd A B ≫ Over.homMk (sec ≫ pullback.fst G.hom B.hom) hsecw) := by
        rw [hδsnd, hEg]
    _ = lift (fst A B ≫ (lift (𝟙 A) (toUnit A ≫ e₂) ≫ f))
          (snd A B ≫ Over.homMk (sec ≫ pullback.fst G.hom B.hom) hsecw) ≫ μ[G] :=
        Hom.mul_def _ _

/-- **(T-W7.7·C2, GIT Cor 6.3, connected-base wrapper)** With `B.left` connected, any
point of the form `e₂(s)` is a fixed point of `e₂ ∘ q` in the unique component. -/
theorem factor_mul_of_tensor {S : Scheme.{u}} [IsLocallyNoetherian S]
    {A B G : Over S} [GrpObj G] [IsLocallyNoetherian B.left]
    [IsProper A.hom] [Flat A.hom] (hO : UniversallyOConnected A.hom)
    (hBconn : ConnectedSpace B.left) (e₁ : 𝟙_ (Over S) ⟶ A) (e₂ : 𝟙_ (Over S) ⟶ B)
    [IsSeparated G.hom] (f : A ⊗ B ⟶ G) :
    ∃ (g : A ⟶ G) (h : B ⟶ G),
      f = lift (fst A B ≫ g) (snd A B ≫ h) ≫ μ[G] := by
  refine factor_mul_of_tensor_of_forall_component hO e₁ e₂ (fun t => ?_) f
  refine ⟨e₂.left.base (B.hom.base t), ?_, ?_⟩
  · haveI := hBconn
    rw [PreconnectedSpace.connectedComponent_eq_univ t]
    trivial
  · exact congrArg
      (fun m : S ⟶ S => e₂.left.base (m.base (B.hom.base t))) (Over.w e₂)

/-- **(T-W7.7a-C3, GIT Cor 6.4, PROVEN)** A pointed morphism of group objects in `Over S`,
whose source is proper flat and universally `O`-connected over a connected locally
noetherian `S`, is a homomorphism (the multiplication-compatibility equation;
unit-compatibility is the hypothesis). Proof: C2 applied to `μ[A] ≫ f` with
`e₁ = e₂ = η[A]` (the total space is connected by C2conn and locally noetherian since
proper is of finite type); then pure Hom-group algebra: restricting the decomposition
`f(xy) = g(x)h(y)` to the two axes gives `f = g·h(e)` and `f = g(e)·h`, the unit identity
gives `g(e)h(e) = 1`, hence `h(e)g(e) = 1` (groups), and
`f(x)f(y) = g(x)·[h(e)g(e)]·h(y) = f(xy)`. `(hconn : ConnectedSpace S)` added to the
skeleton statement (logged, rule 5) — C2conn needs it; C4's arbitrary-loc-noeth reduction
is componentwise, its own leaf. Source: GIT p. 116–117, Cor 6.4 (verbatim in quotes
file). -/
theorem isMonHom_of_one_comp_eq' {S : Scheme.{u}} [IsLocallyNoetherian S]
    {A G : Over S} [GrpObj A] [GrpObj G]
    [IsProper A.hom] [Flat A.hom] (hO : UniversallyOConnected A.hom)
    [IsSeparated G.hom] (f : A ⟶ G) (hη : η[A] ≫ f = η[G]) :
    μ[A] ≫ f = MonoidalCategory.tensorHom f f ≫ μ[G] := by
  -- the total space is locally noetherian
  haveI : IsLocallyNoetherian ↑A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have heA : η[A].left ≫ A.hom = 𝟙 S := Over.w η[A]
  -- every component of the total space contains a fixed point of `η ∘ π`: components are
  -- the fibres of the base's components (open + closed + connected fibres)
  have hcorr := connectedComponent_eq_preimage_connectedComponent
    (f := (A.hom.base : _ → ↥S)) A.hom.base.hom.continuous A.hom.isOpenMap A.hom.isClosedMap
    (fun y => isConnected_fibre_of_universallyOConnected hO η[A].left heA y)
  have hπη : ∀ s : ↥S, A.hom.base (η[A].left.base s) = s := fun s => by
    exact congrArg (fun m : S ⟶ S => m.base s) heA
  have hfix : ∀ t : ↥A.left, ∃ b ∈ connectedComponent t,
      η[A].left.base (A.hom.base b) = b := by
    intro t
    refine ⟨η[A].left.base (A.hom.base t), ?_, ?_⟩
    · rw [hcorr t]
      show A.hom.base (η[A].left.base (A.hom.base t)) ∈ connectedComponent (A.hom.base t)
      rw [hπη (A.hom.base t)]
      exact mem_connectedComponent
    · exact congrArg (fun s => η[A].left.base s) (hπη (A.hom.base t))
  -- the product decomposition of `μ ≫ f` (GIT 6.3, componentwise)
  obtain ⟨g, h, hgh⟩ := factor_mul_of_tensor_of_forall_component hO η[A] η[A] hfix (μ[A] ≫ f)
  have hF : μ[A] ≫ f = (fst A A ≫ g) * (snd A A ≫ h) := hgh
  -- the two axis embeddings compose with `μ` to the identity
  have hi₁ : lift (𝟙 A) (toUnit A ≫ η[A]) ≫ μ[A] = 𝟙 A := by
    show (𝟙 A) * (1 : A ⟶ A) = 𝟙 A
    rw [_root_.mul_one]
  have hi₂ : lift (toUnit A ≫ η[A]) (𝟙 A) ≫ μ[A] = 𝟙 A := by
    show (1 : A ⟶ A) * (𝟙 A) = 𝟙 A
    rw [_root_.one_mul]
  -- restricting the decomposition to the axes: `f = g · h(e)` and `f = g(e) · h`
  have h1 : f = g * (toUnit A ≫ (η[A] ≫ h)) := by
    calc f = lift (𝟙 A) (toUnit A ≫ η[A]) ≫ (μ[A] ≫ f) := by
          rw [← Category.assoc, hi₁, Category.id_comp]
      _ = lift (𝟙 A) (toUnit A ≫ η[A]) ≫ ((fst A A ≫ g) * (snd A A ≫ h)) := by rw [hF]
      _ = (lift (𝟙 A) (toUnit A ≫ η[A]) ≫ (fst A A ≫ g))
            * (lift (𝟙 A) (toUnit A ≫ η[A]) ≫ (snd A A ≫ h)) := MonObj.comp_mul _ _ _
      _ = g * (toUnit A ≫ (η[A] ≫ h)) := by
          rw [← Category.assoc, ← Category.assoc, lift_fst, lift_snd, Category.id_comp,
            Category.assoc]
  have h2 : f = (toUnit A ≫ (η[A] ≫ g)) * h := by
    calc f = lift (toUnit A ≫ η[A]) (𝟙 A) ≫ (μ[A] ≫ f) := by
          rw [← Category.assoc, hi₂, Category.id_comp]
      _ = lift (toUnit A ≫ η[A]) (𝟙 A) ≫ ((fst A A ≫ g) * (snd A A ≫ h)) := by rw [hF]
      _ = (lift (toUnit A ≫ η[A]) (𝟙 A) ≫ (fst A A ≫ g))
            * (lift (toUnit A ≫ η[A]) (𝟙 A) ≫ (snd A A ≫ h)) := MonObj.comp_mul _ _ _
      _ = (toUnit A ≫ (η[A] ≫ g)) * h := by
          rw [← Category.assoc, ← Category.assoc, lift_fst, lift_snd, Category.id_comp,
            Category.assoc]
  -- the unit identity `g(e) · h(e) = 1`, and its group-theoretic flip
  have hone : (η[A] ≫ g) * (η[A] ≫ h) = 1 := by
    have h3 : η[A] ≫ f = (η[A] ≫ g) * (η[A] ≫ h) := by
      calc η[A] ≫ f
          = (η[A] ≫ g) * (η[A] ≫ (toUnit A ≫ (η[A] ≫ h))) := by
            rw [h1]; exact MonObj.comp_mul _ _ _
        _ = (η[A] ≫ g) * (η[A] ≫ h) := by
            congr 1
            rw [← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]
    rw [← h3, hη, Hom.one_def, toUnit_unit, Category.id_comp]
  have hone' : (η[A] ≫ h) * (η[A] ≫ g) = 1 := by
    rw [eq_inv_of_mul_eq_one_left hone, _root_.mul_inv_cancel]
  -- assemble: `f(x)·f(y) = g(x)·[h(e)·g(e)]·h(y) = f(xy)`
  have hfst : fst A A ≫ f = (fst A A ≫ g) * (toUnit (A ⊗ A) ≫ (η[A] ≫ h)) := by
    rw [h1]
    refine (MonObj.comp_mul _ _ _).trans ?_
    congr 1
  have hsnd : snd A A ≫ f = (toUnit (A ⊗ A) ≫ (η[A] ≫ g)) * (snd A A ≫ h) := by
    rw [h2]
    refine (MonObj.comp_mul _ _ _).trans ?_
    congr 1
    rw [← Category.assoc, comp_toUnit]
  have hmid : (toUnit (A ⊗ A) ≫ (η[A] ≫ h)) * (toUnit (A ⊗ A) ≫ (η[A] ≫ g))
      = (1 : A ⊗ A ⟶ G) := by
    rw [← MonObj.comp_mul, hone', MonObj.comp_one]
  have hfinal : (fst A A ≫ f) * (snd A A ≫ f) = (fst A A ≫ g) * (snd A A ≫ h) := by
    rw [hfst, hsnd, _root_.mul_assoc, ← _root_.mul_assoc (toUnit (A ⊗ A) ≫ (η[A] ≫ h)),
      hmid, _root_.one_mul]
  calc μ[A] ≫ f = (fst A A ≫ g) * (snd A A ≫ h) := hF
    _ = (fst A A ≫ f) * (snd A A ≫ f) := hfinal.symm
    _ = lift (fst A A ≫ f) (snd A A ≫ f) ≫ μ[G] := Hom.mul_def _ _
    _ = MonoidalCategory.tensorHom f f ≫ μ[G] := by
        congr 1

/-- **(T-W7.7a-C3, connected-base wrapper)** -/
theorem isMonHom_of_one_comp_eq {S : Scheme.{u}} [IsLocallyNoetherian S]
    (hconn : ConnectedSpace S) {A G : Over S} [GrpObj A] [GrpObj G]
    [IsProper A.hom] [Flat A.hom] (hO : UniversallyOConnected A.hom)
    [IsSeparated G.hom] (f : A ⟶ G) (hη : η[A] ≫ f = η[G]) :
    μ[A] ≫ f = MonoidalCategory.tensorHom f f ≫ μ[G] :=
  isMonHom_of_one_comp_eq' hO f hη

/-- **(T-W7.7·C4conn, GIT Cor 6.6 over a connected base, PROVEN modulo r-supply)**
Canonicity of the group law over a connected locally noetherian base. The two units are
both the zero section (`one_eq_zero`); C3 applied to `𝟙` (viewed from the `grp`-structure
into the `grp'`-structure, pointed by the unit agreement) gives `μ = μ'`; `MonObj.ext`
(the unit is determined by the multiplication) and `GrpObj.ext` (the inverse is
determined) close the structure equality, with the `Prop` fields definitionally
proof-irrelevant. Consumes `EllipticCurveGeom.universallyOConnected` (T-W7.r-supply,
gated on P3's i5). -/
theorem abelEnrichment_unique_of_connectedSpace {S : Scheme.{u}}
    [IsLocallyNoetherian S] (hconn : ConnectedSpace S) (E E' : EllipticCurve S)
    (h : E.toEllipticCurveGeom = E'.toEllipticCurveGeom) : E = E' := by
  obtain ⟨geom, grp, comm, hone⟩ := E
  obtain ⟨geom', grp', comm', hone'⟩ := E'
  obtain rfl : geom = geom' := h
  -- the two units agree: both are the zero section
  have honeeq : (letI := grp; (η[Over.mk geom.π] : 𝟙_ (Over S) ⟶ Over.mk geom.π))
      = (letI := grp'; (η[Over.mk geom.π] : 𝟙_ (Over S) ⟶ Over.mk geom.π)) := by
    apply Over.OverMorphism.ext
    rw [hone, hone']
  -- the two multiplications agree: GIT 6.4 applied to the identity
  have hmul : (letI := grp; (μ[Over.mk geom.π] : Over.mk geom.π ⊗ Over.mk geom.π ⟶ _))
      = (letI := grp'; (μ[Over.mk geom.π] : Over.mk geom.π ⊗ Over.mk geom.π ⟶ _)) := by
    haveI : Smooth geom.π := SmoothOfRelativeDimension.smooth (n := 1) (f := geom.π)
    haveI hP : IsProper (Over.mk geom.π).hom := inferInstanceAs (IsProper geom.π)
    haveI hFl : Flat (Over.mk geom.π).hom := inferInstanceAs (Flat geom.π)
    haveI hSep : IsSeparated (Over.mk geom.π).hom := inferInstanceAs (IsSeparated geom.π)
    have h64 := @isMonHom_of_one_comp_eq S _ hconn (Over.mk geom.π) (Over.mk geom.π)
      grp grp' hP hFl geom.universallyOConnected hSep (𝟙 _)
      (by rw [Category.comp_id]; exact honeeq)
    simpa using h64
  obtain rfl : grp = grp' := GrpObj.ext _ _ (MonObj.ext _ _ hmul)
  rfl

/-- **(T-W7.7 = T-W7b, GIT Cor 6.6)** Canonicity of the group law over a locally noetherian
base: two working records with the same geometry are equal ("Apply Corollary 6.4 to `1_X`,
with 2 different group laws considered on domain and image" — GIT p. 117, verbatim). The
connected case is `abelEnrichment_unique_of_connectedSpace`; the unrestricted-base statement
(`abelEnrichment_unique`) additionally needs EGA IV §8 spreading-out — ticket T-W7.8, off
this path. -/
theorem abelEnrichment_unique_of_isLocallyNoetherian {S : Scheme.{u}}
    [IsLocallyNoetherian S] (E E' : EllipticCurve S)
    (h : E.toEllipticCurveGeom = E'.toEllipticCurveGeom) : E = E' := by
  -- (T-W7.7·C4glue, PROVEN) no componentwise reduction needed after all: the ∀-component
  -- rigidity chain (`rigidity_of_forall_component` → `factor_mul_of_tensor_of_forall_-
  -- component` → `isMonHom_of_one_comp_eq'`) works over any locally noetherian base —
  -- every component of the total space contains a fixed point of `η ∘ π` because the
  -- components of the total space are the fibres of the base's components
  -- (`connectedComponent_eq_preimage_connectedComponent`).
  obtain ⟨geom, grp, comm, hone⟩ := E
  obtain ⟨geom', grp', comm', hone'⟩ := E'
  obtain rfl : geom = geom' := h
  have honeeq : (letI := grp; (η[Over.mk geom.π] : 𝟙_ (Over S) ⟶ Over.mk geom.π))
      = (letI := grp'; (η[Over.mk geom.π] : 𝟙_ (Over S) ⟶ Over.mk geom.π)) := by
    apply Over.OverMorphism.ext
    rw [hone, hone']
  have hmul : (letI := grp; (μ[Over.mk geom.π] : Over.mk geom.π ⊗ Over.mk geom.π ⟶ _))
      = (letI := grp'; (μ[Over.mk geom.π] : Over.mk geom.π ⊗ Over.mk geom.π ⟶ _)) := by
    haveI : Smooth geom.π := SmoothOfRelativeDimension.smooth (n := 1) (f := geom.π)
    haveI hP : IsProper (Over.mk geom.π).hom := inferInstanceAs (IsProper geom.π)
    haveI hFl : Flat (Over.mk geom.π).hom := inferInstanceAs (Flat geom.π)
    haveI hSep : IsSeparated (Over.mk geom.π).hom := inferInstanceAs (IsSeparated geom.π)
    have h64 := @isMonHom_of_one_comp_eq' S _ (Over.mk geom.π) (Over.mk geom.π)
      grp grp' hP hFl geom.universallyOConnected hSep (𝟙 _)
      (by rw [Category.comp_id]; exact honeeq)
    simpa using h64
  obtain rfl : grp = grp' := GrpObj.ext _ _ (MonObj.ext _ _ hmul)
  rfl

end ModularCurves
