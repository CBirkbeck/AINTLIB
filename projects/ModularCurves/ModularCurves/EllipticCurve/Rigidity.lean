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
  sorry

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
