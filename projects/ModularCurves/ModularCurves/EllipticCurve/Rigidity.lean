import ModularCurves.EllipticCurve.GroupLaw
-- NOTE (P4, 2026-07-07): `import ModularCurves.EllipticCurve.PoleFiltration` deliberately
-- deferred to the T-W7.r-supply ticket (which will consume
-- `locallyWeierstrass_pushforward_O_eq_O`); nothing here references it yet, and keeping it
-- out decouples lane P4 builds from lane P3's in-flight file.
import Mathlib.AlgebraicGeometry.Morphisms.Flat
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
  refine ⟨e ≫ f, by rw [Category.assoc, hf, he], ?_⟩
  -- if `X` is empty there is nothing to prove
  by_cases hX : IsEmpty X
  · haveI := hX
    exact isInitialOfIsEmpty.hom_ext _ _
  rw [not_isEmpty_iff] at hX
  obtain ⟨x₀⟩ := hX
  -- both `f` and any candidate factorization land in one affine chart of `Y` at `y₀ := f x₀`
  -- (packaged existentially so that the chart's type does not mention `f`, keeping
  -- rewrite motives type-correct)
  obtain ⟨V, u, hVimm, hVaff, hrange⟩ :
      ∃ (V : Scheme.{u}) (u : V ⟶ Y), IsOpenImmersion u ∧ IsAffine V ∧
        Set.range f.base ⊆ Set.range u.base := by
    refine ⟨_, Y.affineCover.f (Y.affineCover.idx (f.base x₀)), inferInstance,
      inferInstance, fun y hy => ?_⟩
    rw [hone hy ⟨x₀, rfl⟩]
    exact Y.affineCover.covers (f.base x₀)
  haveI := hVimm
  haveI := hVaff
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
  -- Assembly map (P4 session 2026-07-07; every mathlib name verified in this checkout):
  -- * equalizer backbone: `Z := equalizer (Over.homMk f) (Over.homMk (p ≫ e ≫ f))` in
  --   `Over S`; its `ι.left` is a closed immersion by `isClosedImmersion_equalizer_ι_left`
  --   (uses `[IsSeparated q]`).
  -- * seed at `s`: case 1 over `Spec κ(s)` — `rigidity_of_subsingleton_range` +
  --   `UniversallyOConnected.baseChange`; the range-subsingleton hypothesis descends from
  --   `hs` because the base-changed model injects on points (mono pullback).
  -- * thickening at `t ∈ U₁`: case 1 over `Spec (Γ stalk quotient 𝔪ₜⁿ)`, same two lemmas,
  --   giving scheme-theoretic factorization of every infinitesimal fibre through `Z`.
  -- * Krull: on stalks at `x ∈ p⁻¹(t)`, the equalizer ideal lies in `⋂ₙ 𝔪ₜⁿ·O_{X,x} = ⊥`
  --   by `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing` (stalks noetherian: the
  --   `IsLocallyNoetherian` stalk instance; `X` loc. noeth. since `p` is of finite type
  --   over loc. noeth. `S`); coherence + properness (`p` closed) upgrade stalk vanishing
  --   near the fibre to `p ⁻¹ᵁ U₀ ⟶ X` factoring through `Z`, `U₀ ∋ t` open.
  -- * clopen: `U₁ := S ∖ p.base '' (X ∖ range ι.left)` is closed since `p` is an open map
  --   (`UniversallyOpen.of_flat`: `[Flat p]` + `LocallyOfFinitePresentation` from
  --   properness over a locally noetherian base) and open by the Krull neighbourhoods;
  --   `hconn` + `s ∈ U₁` give `U₁ = S`; the neighbourhood factorizations glue (`ι` mono),
  --   so `ι.left` is a split-epi closed immersion, hence an iso, hence `f = p ≫ (e ≫ f)`.
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
