import ModularCurves.EllipticCurve.GroupLaw
import ModularCurves.EllipticCurve.PoleFiltration
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
  sorry

/-- **(T-W7.7a-R1′, GIT case 1)** Rigidity over a one-point base: if the base's carrier is a
single point (e.g. `Spec` of an Artinian local ring), a morphism `f : X ⟶ Y` over `S` with
`X` universally `O`-connected over `S` factors through a section of `Y ⟶ S`, via `η := f∘e`
made scheme-theoretic by the ringed-space argument. The Artinian instances of this lemma
drive the thickening step of case 2. Source: GIT p. 115, case 1 (verbatim in quotes file). -/
theorem rigidity_of_subsingleton_base {X Y S : Scheme.{u}}
    (hS : ∀ a b : S, a = b)
    {p : X ⟶ S} (hp : UniversallyOConnected p) (e : S ⟶ X) (he : e ≫ p = 𝟙 S)
    {q : Y ⟶ S} [IsSeparated q] (f : X ⟶ Y) (hf : f ≫ q = p) :
    ∃ sec : S ⟶ Y, sec ≫ q = 𝟙 S ∧ f = p ≫ sec := by
  sorry

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
