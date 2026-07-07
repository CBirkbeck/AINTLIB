import ModularCurves.EllipticCurve.GroupLaw
-- NOTE (P4, 2026-07-07): `import ModularCurves.EllipticCurve.PoleFiltration` deliberately
-- deferred to the T-W7.r-supply ticket (which will consume
-- `locallyWeierstrass_pushforward_O_eq_O`); nothing here references it yet, and keeping it
-- out decouples lane P4 builds from lane P3's in-flight file.
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian

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

/-- **(T-W7.7a-hyp-supply)** Locally-Weierstrass families are universally `O`-connected:
base changes are again locally Weierstrass (`LocallyWeierstrass.baseChange`), so the uniform
global-sections theorem instantiates. -/
theorem EllipticCurveGeom.universallyOConnected {S : Scheme.{u}} (G : EllipticCurveGeom S) :
    UniversallyOConnected G.π := by
  sorry

/-- Morphisms into an affine scheme are determined by their pullback on global sections
(the `Γ`–`Spec` adjunction, in the form every rigidity argument below consumes). -/
theorem hom_ext_of_isAffine {W Z : Scheme.{u}} [IsAffine Z] {f g : W ⟶ Z}
    (h : f.appTop = g.appTop) : f = g := by
  rw [← cancel_mono Z.isoSpec.hom, Scheme.isoSpec, asIso_hom,
    Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality, h]

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
    (x : X) (hset : p.base ⁻¹' {p.base x} ⊆ Set.range (eqLocusι f g hf hg).base)
    (U : X.affineOpens) (hxU : x ∈ U.1) (a : Γ(X, U.1))
    (ha : a ∈ (eqLocusι f g hf hg).ker.ideal U) (n : ℕ) :
    X.presheaf.germ U.1 x hxU a ∈
      (Ideal.map (p.stalkMap x).hom
        (IsLocalRing.maximalIdeal (S.presheaf.stalk (p.base x)))) ^ n := by
  sorry

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
    (f g : X ⟶ Y) (hf : f ≫ q = p) (hg : g ≫ q = p) (t : S)
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
        fun n => germ_ker_mem_pow_of_fibre_subset hp e he f g hf hg x
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

/-- **(T-W7.r2·d, clopen assembly — SORRIED LEAF)** On a connected base, if the agreement
locus contains one fibre set-theoretically and every set-theoretic fibre containment
upgrades to an open scheme-theoretic one (the Krull leaf), then the identity of `X`
factors through the locus. Attack route: `U₁ := {t | p⁻¹(t) ⊆ range ι}` contains `s`, is
open by the Krull leaf, and is closed because `U₁ = S ∖ p(X ∖ range ι)` with `p` an open
map (`UniversallyOpen.of_flat`: `Flat` + `LocallyOfFinitePresentation` from properness over
a locally noetherian base); connectedness gives `U₁ = S`; the open factorizations glue
along `⨆ = ⊤` since `eqLocusι` is a monomorphism (closed immersion), giving the global
factorization. -/
theorem exists_factor_of_connected [IsLocallyNoetherian S] [IsProper p] [Flat p]
    (hconn : ConnectedSpace S)
    (hp : UniversallyOConnected p) (e : S ⟶ X) (he : e ≫ p = 𝟙 S)
    (f g : X ⟶ Y) (hf : f ≫ q = p) (hg : g ≫ q = p) (s : S)
    (hseed : p.base ⁻¹' {s} ⊆ Set.range (eqLocusι f g hf hg).base) :
    ∃ w : X ⟶ eqLocus f g hf hg, w ≫ eqLocusι f g hf hg = 𝟙 X := by
  classical
  haveI := hconn
  -- the locus of set-theoretic fibrewise containment
  set U₁ : Set S := {t | p.base ⁻¹' {t} ⊆ Set.range (eqLocusι f g hf hg).base} with hU₁
  -- open, by the Krull-neighbourhood leaf
  have hopen : IsOpen U₁ := by
    rw [isOpen_iff_forall_mem_open]
    intro t ht
    obtain ⟨U₀, htU₀, w₀, hw₀⟩ := exists_open_factor_of_fibre_subset hp e he f g hf hg t ht
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
  -- connectedness: the clopen locus containing `s` is everything
  have huniv : U₁ = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨s, hseed⟩
  -- choose a factorization neighbourhood around every point
  have hmem : ∀ t : S, p.base ⁻¹' {t} ⊆ Set.range (eqLocusι f g hf hg).base := fun t => by
    have ht : t ∈ U₁ := by rw [huniv]; trivial
    exact ht
  have hall : ∀ t : S, ∃ U₀ : S.Opens, t ∈ U₀ ∧
      ∃ w : ((p ⁻¹ᵁ U₀) : X.Opens).toScheme ⟶ eqLocus f g hf hg,
        w ≫ eqLocusι f g hf hg = ((p ⁻¹ᵁ U₀) : X.Opens).ι :=
    fun t => exists_open_factor_of_fibre_subset hp e he f g hf hg t (hmem t)
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
  obtain ⟨w, hw⟩ := exists_factor_of_connected hconn hp e he f (p ≫ (e ≫ f)) hf hg s
    (fibre_subset_eqLocus_of_collapsed hp e he f hf s hs)
  calc f = (w ≫ eqLocusι f (p ≫ (e ≫ f)) hf hg) ≫ f := by rw [hw, Category.id_comp]
    _ = w ≫ (eqLocusι f (p ≫ (e ≫ f)) hf hg ≫ f) := Category.assoc _ _ _
    _ = w ≫ (eqLocusι f (p ≫ (e ≫ f)) hf hg ≫ (p ≫ (e ≫ f))) :=
        congrArg (w ≫ ·) (eqLocusι_comp_eq f (p ≫ (e ≫ f)) hf hg)
    _ = (w ≫ eqLocusι f (p ≫ (e ≫ f)) hf hg) ≫ (p ≫ (e ≫ f)) := (Category.assoc _ _ _).symm
    _ = p ≫ (e ≫ f) := by rw [hw, Category.id_comp]

/-! ### The corollary chain, split (coordinator §2): C1 (Cor 6.2) → C2 (Cor 6.3) → C3 -/

/-- **(T-W7.7·C2conn — SORRIED LEAF, found by the hypothesis sweep)** The total space of a
proper flat universally-`O`-connected family with a section over a connected base is
connected — GIT Cor 6.3 runs its connectedness argument along the SECOND factor, so C3's
application to `A ⊗ A` needs `A.left` connected, not just `S`. No single mathlib name
(2026-07-07). Route: clopen `C ⊆ X` meets every fibre in a clopen set; fibres are connected
(`O`-connectedness at residue fields); `p` open (flat + lfp) and closed (proper) makes
`p(C)` clopen in connected `S`; the section decides which side is full. -/
theorem connectedSpace_of_universallyOConnected {X S : Scheme.{u}} {p : X ⟶ S}
    [IsProper p] [Flat p] (hp : UniversallyOConnected p) (e : S ⟶ X) (he : e ≫ p = 𝟙 S)
    [hconn : ConnectedSpace S] : ConnectedSpace X := by
  sorry

/-- **(T-W7.7·C1, GIT Cor 6.2 — SORRIED LEAF)** Two `S`-morphisms from a proper flat
universally-`O`-connected `A` into a separated group object `G` that agree on ONE fibre
differ by a constant section: `f = (χ ∘ toUnit) · g` for a point `χ` of `G`. Proof route:
apply `rigidity` to the pointwise quotient `lift f g ≫ (𝟙 ⊗ ι[G]) ≫ μ[G]` (the GIT `f·g⁻¹`),
whose collapsed fibre is supplied by the fibre-equality hypothesis. Source: GIT p. 116,
Cor 6.2 (verbatim in quotes file). -/
theorem eq_mul_of_fibre_eq {S : Scheme.{u}} [IsLocallyNoetherian S]
    (hconn : ConnectedSpace S) {A G : Over S} [GrpObj G]
    [IsProper A.hom] [Flat A.hom] (hO : UniversallyOConnected A.hom)
    [IsSeparated G.hom] (f g : A ⟶ G) (s : S)
    (hfib : pullback.fst A.hom (S.fromSpecResidueField s) ≫ f.left =
      pullback.fst A.hom (S.fromSpecResidueField s) ≫ g.left) :
    ∃ χ : 𝟙_ (Over S) ⟶ G, f = lift (toUnit A ≫ χ) g ≫ μ[G] := by
  sorry

/-- **(T-W7.7·C2, GIT Cor 6.3 — SORRIED LEAF)** A morphism `A ⊗ B ⟶ G` out of a product,
with `A` proper flat universally-`O`-connected carrying a unit point and `B.left`
connected, splits as a product `f(x,y) = g(x)·h(y)`. Proof route: GIT — apply C1 to the
`B`-family of morphisms `f` vs `f(e₁, ·)` (connectedness running along `B`, supplied for
the C3 application by `connectedSpace_of_universallyOConnected`). Source: GIT p. 116,
Cor 6.3 (verbatim in quotes file). -/
theorem factor_mul_of_tensor {S : Scheme.{u}} [IsLocallyNoetherian S]
    {A B G : Over S} [GrpObj G]
    [IsProper A.hom] [Flat A.hom] (hO : UniversallyOConnected A.hom)
    (hBconn : ConnectedSpace B.left) (e₁ : 𝟙_ (Over S) ⟶ A)
    [IsSeparated G.hom] (f : A ⊗ B ⟶ G) :
    ∃ (g : A ⟶ G) (h : B ⟶ G),
      f = lift (fst A B ≫ g) (snd A B ≫ h) ≫ μ[G] := by
  sorry

/-- **(T-W7.7a-C3, GIT Cor 6.4)** A pointed morphism of group objects in `Over S`, whose
source is proper flat and universally `O`-connected over a locally noetherian `S`, is a
homomorphism (the multiplication-compatibility equation; unit-compatibility is the
hypothesis). Proof: GIT 6.2/6.3 (differences of morphisms into a group object; the product
decomposition `f(x,y) = g(x)·h(y)`, connectedness running along the second factor,
componentwise over `S`) applied to `μ[A] ≫ f`. Source: GIT p. 116–117, Cor 6.2–6.4
(verbatim in quotes file). -/
theorem isMonHom_of_one_comp_eq {S : Scheme.{u}} [IsLocallyNoetherian S]
    {A G : Over S} [GrpObj A] [GrpObj G]
    [IsProper A.hom] [Flat A.hom] (hO : UniversallyOConnected A.hom)
    [IsSeparated G.hom] (f : A ⟶ G) (hη : η[A] ≫ f = η[G]) :
    μ[A] ≫ f = MonoidalCategory.tensorHom f f ≫ μ[G] := by
  sorry

/-- **(T-W7.7 = T-W7b, GIT Cor 6.6)** Canonicity of the group law over a locally noetherian
base: two working records with the same geometry are equal. Proof: apply the pointed-implies-
homomorphism corollary to the identity morphism, with the two group structures on domain and
codomain ("Apply Corollary 6.4 to `1_X`, with 2 different group laws considered on domain and
image" — GIT p. 117, verbatim). The unrestricted-base statement (`abelEnrichment_unique`)
additionally needs EGA IV §8 spreading-out — ticket T-W7.8, off this path. -/
theorem abelEnrichment_unique_of_isLocallyNoetherian {S : Scheme.{u}}
    [IsLocallyNoetherian S] (E E' : EllipticCurve S)
    (h : E.toEllipticCurveGeom = E'.toEllipticCurveGeom) : E = E' := by
  sorry

end ModularCurves
