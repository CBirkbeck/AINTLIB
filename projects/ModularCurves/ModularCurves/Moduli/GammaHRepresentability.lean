/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

STREAM-GH skeleton (T-H4 corrected + route to T-H6). Decomposition of record:
`.mathlib-quality/decomposition-gammah-route.md` (2026-07-08).
-/
import ModularCurves.Moduli.GammaH
import ModularCurves.Moduli.QuotientProblem
import ModularCurves.Moduli.LevelSpaces
import ModularCurves.ModularCurve.YFullRoute

/-!
# Γ_H relative representability (Loeffler 3.8.2 / KM 3.7.1 + 7.1) — corrected statements

**Loeffler Prop 3.8.2 (verbatim)**: "P_H is relatively representable and étale over
Ell/ℤ[1/N] (i.e. for all E/S ∈ Ob(Ell/ℤ[1/N]), the functor T ↦ P_H(E ×_S T) is
represented by an étale S-scheme). *Proof.* For H = {1}, for E/S ∈ Ob(Ell/ℤ[1/N]), we
can find an explicit S-scheme representing P_H on Sch/S; it is an open subscheme of
E[N] ×_S E[N] given by non-vanishing of Weil pairings. For general H just take the
quotient of this by H."

**THE CORRECTION OF RECORD (F1, adversarial pass 2026-07-08 — B2 statement event).**
The held statements `gammaHNaive_relativelyRepresentable` (T-H4) and
`gammaHNaive_representable_of_rigid` (T-H6) in `Moduli/GammaH.lean` assert relative
representability / representability of `gammaHNaiveProblem R N H`, whose value at `E/S`
is the set of **global** `H`-orbits of full level structures. That presheaf is not a
Zariski sheaf for `H ≠ ⊥` (over `T ⊔ T` the classes `[(L,L)]` and `[(L,γL)]`, `γ ≠ 1`,
are distinct — the `H`-action on level structures over a nonempty base is free — yet
restrict equally to both components), so it is not (relatively) representable:
`gammaHNaiveProblem_not_relativelyRepresentable` below. The sources define `P_H`
differently: Loeffler Fact 3.8.1 pins `P_H` **only on algebraically closed points**
("There exists a moduli problem P_H … such that if k̄ is algebraically closed …
P_H(E/k̄) = {H-orbits of isomorphisms (ℤ/N)² ≅ E[N]}"), his §3.6 notes the naive orbit
map "is neither injective nor surjective" in general, and Katz–Mazur define the
general-`H` problem as the **quotient moduli problem** of KM 7.1.2, pinned by

> "(Q1): G operates trivially on 𝒫′. (Q2): … for every modular family of elliptic
> curves E/S/R, the quotient scheme (𝒫_{E/S})/G exists, and maps isomorphically to
> (𝒫′)_{E/S}."

with existence and properties given by **KM THEOREM 7.1.3** (𝒫 relatively representable
and affine over (Ell/R), G finite): the quotient exists as a relatively representable
problem, `𝒫 → 𝒫/G` is finite, and — when G acts freely — `𝒫_{E/S}` is a finite étale
G-torsor over `(𝒫/G)_{E/S}` and quotient formation commutes with base change
(7.1.3(2),(3c),(4)). This file states that development:

* `ModuliProblem.FreeAction`, `ModuliProblem.EquivariantRelRepData`,
  `ModuliProblem.QuotientProblemData` — the KM 7.1.1/7.1.2 vocabulary (§ PART 0);
* `gammaHAut` (DS-GH1) — the Fact 3.8.1 `H`-action on the full-level problem;
* the H = 1 half via the T-D18/T-W8 level scheme (`levelSpaceΓπ` finite; étale =
  the Weil-pairing leaf, gate [DS4/T-C1]) (§ PART A);
* the generic quotient step, KM 7.1.3 (gates [A711-FP], [A711-BC]) (§ PART B);
* corrected T-H4/T-H6, the `⊥`-bridge (which *discharges* the held statement at
  `H = ⊥`), the Fact-3.8.1 comparison bridge, and the F1 refutation (§ PART C).

Held files are never edited; all bridges toward `Moduli/GammaH.lean`'s declarations are
stated here.
-/

open AlgebraicGeometry CategoryTheory Limits

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

/-! ### PART 0 — vocabulary: free actions, equivariant relative data, quotient problems

KM 7.1.1 (verbatim): "Let R be a ring, G a finite group, and 𝒫 a moduli problem on
(Ell/R). We say that G operates on 𝒫 if for every R-scheme S, and every elliptic curve
E/S, the group G operates on the set 𝒫(E/S) in such a way that for every morphism in
(Ell/R), viewed as a Cartesian diagram … the obvious diagram of actions below commutes
[7.1.1.1]. If 𝒫 is relatively representable, then for every E/S, the group G acts on
the S-scheme 𝒫_{E/S}." -/

namespace ModuliProblem

variable {R : CommRingCat.{u}}

/-- **[GH0a] (KM 7.1.3(2), the freeness hypothesis)** — verbatim: "G operates freely on
𝒫, in the sense that for every E/S/R, G operates freely on the set 𝒫(E/S)". Honest
Lean form over nonempty bases (over the empty base every action has a fixed value set;
same adjudication as T-H7's DEF-1 guard and `simulSchemeAction_free_of_rigid`'s
`IsEmpty` convention). -/
def FreeAction {Q : ModuliProblem R} {G : Type*} [Group G] (φ : G →* Aut Q) : Prop :=
  ∀ X : EllObj R, Nonempty X.base → ∀ γ : G, γ ≠ 1 →
    ∀ a : Q.obj (Opposite.op X), (φ γ).hom.app (Opposite.op X) a ≠ a

/-- **[GH0b] (KM 7.1.1 + 3.7.1 conclusion, bundled)** A relative representation datum
for `Q` at `X` carrying a compatible `G`-action on the representing scheme, with the
structure map finite étale. This is `TorsorData` (T-Q6, `Moduli/QuotientProblem.lean`)
*minus* its `surjective`/`torsor` fields — those axioms hold only for the full
`GL₂`-torsor, not for the `H ⊊ GL₂` data quotiented in KM 7.1. Field conventions
(`σZ`/`over_base`/`equivariant`) are copied verbatim from `TorsorData` (q-lane
attack-adjudicated) so the two structures interoperate. -/
structure EquivariantRelRepData {Q : ModuliProblem R} {G : Type*} [Group G] [Finite G]
    (φ : G →* Aut Q) (X : EllObj R) extends RelRepData Q X where
  /-- The `G`-action on the relative representing scheme (KM 7.1.1's closing
  sentence). -/
  σZ : SchemeAction G Z
  /-- The action lies over the base. -/
  over_base : ∀ γ : G, σZ.hom γ ≫ f = f
  /-- The representing bijections are `G`-equivariant (diagram KM 7.1.1.1). -/
  equivariant : ∀ {T : Scheme.{u}} (g : T ⟶ X.base)
    (h : { h : T ⟶ Z // h ≫ f = g }) (γ : G),
    eqv g ⟨h.1 ≫ σZ.hom γ, by rw [Category.assoc, over_base, h.2]⟩ =
      (φ γ).hom.app (Opposite.op (X.pullbackAlong g)) (eqv g h)
  /-- The structure map is finite (KM 3.7.1: "a finite etale S-scheme"). -/
  finite : IsFinite f
  /-- The structure map is étale. -/
  etale : Etale f

/-- **[GH0c] (KM 7.1.2 + 7.1.3(1),(3))** The quotient moduli problem `Q/G`, bundled:
the receiving problem `prob`, the projection `proj : Q ⟶ prob`, its `G`-invariance
(Q1-side), relative representability by finite étale morphisms (7.1.3(1) with the
étale conjunct of 3.7.1/4.7.1), the couniversal property (7.1.3(1) verbatim: "For any
relatively representable 𝒫′, with trivial G-action, any G-equivariant map 𝒫 → 𝒫′
factors uniquely through the projection 𝒫 → 𝒫/G"), and the geometric-point clauses
(7.1.3(3) "bijective on geometric points"; Loeffler Fact 3.8.1's k̄-pin — over `Spec k`
non-closed both fail by twists, Loeffler §3.6). KM's (Q2) quotient-scheme
identification is delivered by the assembly `exists_quotientProblemData`, not carried
as a field (it would freeze a chosen T-Q5 construction into the public structure). -/
structure QuotientProblemData {Q : ModuliProblem R} {G : Type*} [Group G] [Finite G]
    (φ : G →* Aut Q) where
  /-- The quotient problem `Q/G`. -/
  prob : ModuliProblem R
  /-- The projection `Q ⟶ Q/G`. -/
  proj : Q ⟶ prob
  /-- The projection coequalizes the action (KM (Q1)-side). -/
  proj_invariant : ∀ γ : G, (φ γ).hom ≫ proj = proj
  /-- KM 7.1.3(1) + the étale conjunct: `Q/G` is relatively representable by finite
  étale morphisms. -/
  relRep : ∀ X : EllObj R, ∃ d : RelRepData prob X, IsFinite d.f ∧ Etale d.f
  /-- KM 7.1.3(1), verbatim (rel-repr restriction is KM's). -/
  couniversal : ∀ P' : ModuliProblem R, P'.RelativelyRepresentable →
    ∀ ν' : Q ⟶ P', (∀ γ : G, (φ γ).hom ≫ ν' = ν') →
      ∃! μ : prob ⟶ P', proj ≫ μ = ν'
  /-- Over an algebraically closed field, every value of `Q/G` lifts to `Q`
  (KM 7.1.3(3): the comparison is "bijective on geometric points"; surjectivity half). -/
  geom_surjective : ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (sm : Spec (CommRingCat.of k) ⟶ Spec R)
    (E : EllipticCurve (Spec (CommRingCat.of k))),
    Function.Surjective
      (proj.app (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R)))
  /-- Over an algebraically closed field, the fibres of `proj` are exactly the
  `G`-orbits (injectivity half of KM 7.1.3(3); Loeffler Fact 3.8.1's "H-orbits"). -/
  geom_orbits : ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (sm : Spec (CommRingCat.of k) ⟶ Spec R)
    (E : EllipticCurve (Spec (CommRingCat.of k)))
    (a b : Q.obj (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R))),
    proj.app (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R)) a =
        proj.app (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R)) b ↔
      ∃ γ : G, (φ γ).hom.app (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R)) a = b

/-- **[GHB1] (KM 7.1.1, closing sentence)** — "If 𝒫 is relatively representable, then
for every E/S, the group G acts on the S-scheme 𝒫_{E/S}": a problem-level action
transports through any finite étale relative representation datum. The action of `γ`
on `d.Z` is the classifying map of `(φ γ)` applied to the universal element; the
relative mirror of `RepresentableBy.transportHom`/`autMulHom`
(`ForMathlib/RepresentableAut.lean`, PROVEN at the absolute level). If the transport
lands anti-homomorphic (contravariance), the inverse twist is absorbed HERE, never in
consumers. -/
theorem RelRepData.exists_equivariant {Q : ModuliProblem R} {G : Type*} [Group G]
    [Finite G] (φ : G →* Aut Q) {X : EllObj R} (d : RelRepData Q X)
    (hfin : IsFinite d.f) (het : Etale d.f) :
    Nonempty (EquivariantRelRepData φ X) := by
  sorry

/-- **[GHB2] (scheme-level freeness from moduli freeness)** — the form consumed by the
quotient-torsor layer (house shape of `simulSchemeAction_free_of_rigid`'s conclusion):
no `γ ≠ 1` fixes a `T`-point of the representing scheme for nonempty `T`. A fixed
`T`-point is (via `eqv` + `equivariant`) a `γ`-fixed value of `Q` over `E ×_S T` with
`T` nonempty, killed by `FreeAction`. The chart-level Chase–Harrison–Rosenberg form
(KM A7.1.1's "for any non-zero R-algebra R′ … g operates without fixed points on
Hom_{R-alg}(A, R′)", `IsFreeAlgebraAction`) is derived from this inside [GHB4]/[GHB5]'s
proofs. -/
theorem EquivariantRelRepData.free_on_points {Q : ModuliProblem R} {G : Type*}
    [Group G] [Finite G] {φ : G →* Aut Q} {X : EllObj R}
    (e : EquivariantRelRepData φ X) (hfree : FreeAction φ) :
    ∀ {T : Scheme.{u}} (t : T ⟶ e.Z) (γ : G), γ ≠ 1 →
      t ≫ e.σZ.hom γ = t → IsEmpty T := by
  sorry

end ModuliProblem

/-! ### PART B (generic half) — the quotient step: KM 7.1.3 for a finite étale
affine-over-base action

Loeffler's entire quotient step is one sentence ("For general H just take the quotient
of this by H"); the content is KM THEOREM 7.1.3, whose scheme-level core is stated
here generically (a `SchemeAction` on a scheme affine over a base), consuming the
T-Q3/T-Q5 quotient machinery (`ForMathlib/AffineQuotient.lean`,
`ForMathlib/SchemeQuotient.lean` — both sorry-free) and the T-Q2 InvariantTorsor layer.
`/cleanup` may relocate this section to `ForMathlib/`. -/

section SchemeQuotientLayer

/-- The base change of a scheme action lying over `S` along `g : T ⟶ S`: the induced
action on `pullback f g` (trivial on the `T`-leg). Needed to *state* KM 7.1.3(3c). -/
noncomputable def _root_.AlgebraicGeometry.SchemeAction.basePullback
    {G : Type*} [Group G] {Z S T : Scheme.{u}}
    (σ : SchemeAction G Z) (f : Z ⟶ S) (hover : ∀ γ : G, σ.hom γ ≫ f = f)
    (g : T ⟶ S) : SchemeAction G (pullback f g) where
  hom γ := pullback.map f g f g (σ.hom γ) (𝟙 T) (𝟙 S)
    (by rw [Category.comp_id, hover γ]) (by rw [Category.comp_id, Category.id_comp])
  hom_one := by sorry
  hom_mul := by sorry

/-- **[GHB3] (KM 7.1.3(3) existence half; Loeffler Prop 3.6.1's affine patching)** —
"For any E/S/R, the quotient scheme 𝒫_{E/S}/G exists"; Loeffler 3.6.1 (verbatim): "for
X = Spec(A) affine, Spec(A^G) works, and one can show that these patch nicely. (One
needs quasiprojectiveness and finiteness of G here.)" — our patching datum is the
`IsAffineHom`-preimage atlas of affine opens of `S` (stable by `hover`, affine by
`IsAffineHom`), fed to `SchemeAction.quotient`/`quotientπ`/`hom_quotientπ`/
`quotientπ_hom_ext`/`existsUnique_quotientπ_lift` (T-Q5, all PROVEN); `f₀` is the
unique descent of the invariant `f`. -/
theorem _root_.AlgebraicGeometry.SchemeAction.exists_quotient_of_isAffineHom
    {G : Type*} [Group G] [Finite G]
    {Z S : Scheme.{u}} [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from Z))]
    (σ : SchemeAction G Z) (f : Z ⟶ S) [IsAffineHom f]
    (hover : ∀ γ : G, σ.hom γ ≫ f = f) :
    ∃ (Z₀ : Scheme.{u}) (π : Z ⟶ Z₀) (f₀ : Z₀ ⟶ S), π ≫ f₀ = f ∧
      (∀ γ : G, σ.hom γ ≫ π = π) ∧
      ∀ {Y : Scheme.{u}} (F : Z ⟶ Y), (∀ γ : G, σ.hom γ ≫ F = F) →
        ∃! q : Z₀ ⟶ Y, π ≫ q = F := by
  -- The `IsAffineHom`-preimage atlas: an affine open of `S` around each `f x`, pulled back.
  have hcov : ∀ x : Z, ∃ W : S.Opens, IsAffineOpen W ∧ f.base x ∈ W := fun x => by
    obtain ⟨W, hW, hmem, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := S) (TopologicalSpace.Opens.mem_top (f.base x))
    exact ⟨W, hW, hmem⟩
  choose US hUS_aff hUS_mem using hcov
  -- Each `f ⁻¹ᵁ (US x)` is `σ`-stable (immediate from `hover`) and affine (`f` affine).
  have hVs : ∀ x : Z, σ.IsStableOpen (f ⁻¹ᵁ US x) := by
    intro x g
    show (σ.hom g ≫ f) ⁻¹ᵁ US x = f ⁻¹ᵁ US x
    rw [hover g]
  have hVa : ∀ x : Z, IsAffineOpen (f ⁻¹ᵁ US x) := fun x => (hUS_aff x).preimage f
  have hVmem : ∀ x : Z, x ∈ f ⁻¹ᵁ US x := fun x => hUS_mem x
  -- `f₀` is the unique descent of the invariant `f` along the quotient projection.
  obtain ⟨f₀, hf₀, -⟩ :=
    σ.existsUnique_quotientπ_lift (fun x => f ⁻¹ᵁ US x) hVs hVa hVmem f hover
  refine ⟨σ.quotient (fun x => f ⁻¹ᵁ US x) hVs hVa,
    σ.quotientπ (fun x => f ⁻¹ᵁ US x) hVs hVa hVmem, f₀, hf₀,
    fun γ => σ.hom_quotientπ (fun x => f ⁻¹ᵁ US x) hVs hVa hVmem γ, ?_⟩
  intro Y F hF
  exact σ.existsUnique_quotientπ_lift (fun x => f ⁻¹ᵁ US x) hVs hVa hVmem F hF

/-- **[GHB4] (KM 7.1.3(2),(4) — gate [A711-FP])** — verbatim: "If G operates freely on
𝒫 … 𝒫_{E/S} is an etale G-torsor over (𝒫/G)_{E/S}"; "(4) The morphism 𝒫 → 𝒫/G is
finite." Chart-locally: `Aᴳ → A` is finite projective (PROVEN,
`Module.Finite/Projective.of_isFreeAlgebraAction`), a torsor (PROVEN,
`torsorMul_bijective_of_isFreeAlgebraAction`, v10.31), and étale
(`Algebra.Etale.of_isFreeAlgebraAction` — SORRIED, [A711-FP]; the noetherian version
is PROVEN and covers the `Y(N)` pipeline). Stated against ANY datum satisfying the
quotient universal property (all such are canonically isomorphic). -/
theorem _root_.AlgebraicGeometry.SchemeAction.quotientπ_finite_etale_surjective
    {G : Type*} [Group G] [Finite G]
    {Z S Z₀ : Scheme.{u}} (σ : SchemeAction G Z) (f : Z ⟶ S) [IsAffineHom f]
    (hover : ∀ γ : G, σ.hom γ ≫ f = f)
    (hfree : ∀ {T : Scheme.{u}} (t : T ⟶ Z) (γ : G), γ ≠ 1 →
      t ≫ σ.hom γ = t → IsEmpty T)
    (π : Z ⟶ Z₀) (f₀ : Z₀ ⟶ S) (hπf : π ≫ f₀ = f)
    (hπinv : ∀ γ : G, σ.hom γ ≫ π = π)
    (hdesc : ∀ {Y : Scheme.{u}} (F : Z ⟶ Y), (∀ γ : G, σ.hom γ ≫ F = F) →
      ∃! q : Z₀ ⟶ Y, π ≫ q = F) :
    IsFinite π ∧ Etale π ∧ Surjective π := by
  sorry

/-- **[GHB5] (KM 7.1.3(3c) — gate [A711-BC]; the crux of (Q2))** — verbatim: "there is
a natural S-morphism (𝒫_{E/S})/G → (𝒫/G)_{E/S}, which is bijective on geometric
points. It is an isomorphism if any of the following conditions hold: … c) G operates
freely on 𝒫." Formulated as: the base change `pullback f₀ g` of a quotient satisfies
the quotient universal property for the base-changed action — so "quotient commutes
with base change" for free actions. Chart-local algebra core:
`fixedPointsBaseChange_bijective_of_isFreeAlgebraAction`
(`ForMathlib/InvariantTorsor.lean`, KM A7.1.2 "∗(A, G, R, R′) for every R′" — SORRIED,
[A711-BC]); without freeness the statement is FALSE (KM lists (c) as a sufficient
condition; non-free quotients do not commute with base change). -/
theorem _root_.AlgebraicGeometry.SchemeAction.exists_quotient_baseChange_of_free
    {G : Type*} [Group G]
    [Finite G] {Z S Z₀ : Scheme.{u}} (σ : SchemeAction G Z) (f : Z ⟶ S)
    [IsAffineHom f] (hover : ∀ γ : G, σ.hom γ ≫ f = f)
    (hfree : ∀ {T : Scheme.{u}} (t : T ⟶ Z) (γ : G), γ ≠ 1 →
      t ≫ σ.hom γ = t → IsEmpty T)
    (π : Z ⟶ Z₀) (f₀ : Z₀ ⟶ S) (hπf : π ≫ f₀ = f)
    (hπinv : ∀ γ : G, σ.hom γ ≫ π = π)
    (hdesc : ∀ {Y : Scheme.{u}} (F : Z ⟶ Y), (∀ γ : G, σ.hom γ ≫ F = F) →
      ∃! q : Z₀ ⟶ Y, π ≫ q = F)
    {T : Scheme.{u}} (g : T ⟶ S) :
    ∃ πT : pullback f g ⟶ pullback f₀ g,
      πT ≫ pullback.snd f₀ g = pullback.snd f g ∧
      πT ≫ pullback.fst f₀ g = pullback.fst f g ≫ π ∧
      (∀ γ : G, (σ.basePullback f hover g).hom γ ≫ πT = πT) ∧
      ∀ {Y : Scheme.{u}} (F : pullback f g ⟶ Y),
        (∀ γ : G, (σ.basePullback f hover g).hom γ ≫ F = F) →
          ∃! q : pullback f₀ g ⟶ Y, πT ≫ q = F := by
  sorry

/-- **[GHB6] (KM 7.1.3(6), freeness-sharpened)** — KM: "If 𝒫 is finite over (Ell/R),
and R is noetherian, then 𝒫/G is finite over (Ell/R)"; with the projection finite
étale *surjective* (freeness, [GHB4]) both finiteness and étaleness of `f₀` follow
with no noetherian hypothesis: primary route chart-local (`Aᴳ` is a `B`-module direct
summand of the finite `B`-module `A` via the PROVEN projectivity layer; étale via
summand-flatness + unramified quotient), fallback route by descent along the
faithfully flat finite `π` (check mathlib property-descent coverage at execution; if
absent, cut [GH-DESC-GAP]). -/
theorem _root_.AlgebraicGeometry.isFinite_etale_of_comp_of_finite_etale_surjective
    {Z Z₀ S : Scheme.{u}}
    (π : Z ⟶ Z₀) (f₀ : Z₀ ⟶ S) [IsFinite π] [Etale π] [Surjective π]
    (hfin : IsFinite (π ≫ f₀)) (het : Etale (π ≫ f₀)) :
    IsFinite f₀ ∧ Etale f₀ := by
  sorry

end SchemeQuotientLayer

namespace ModuliProblem

variable {R : CommRingCat.{u}}

/-- **[GHB7] (THE ASSEMBLY — KM 7.1.2 + 7.1.3(1),(2),(3); gates through
[GHB4]/[GHB5])** For a free action on a moduli problem with finite étale equivariant
relative data at every object, the quotient problem exists: KM 7.1.3(1) verbatim,
"The quotient 𝒫/G exists as a relatively representable moduli problem, affine over
(Ell/R). For any relatively representable 𝒫′, with trivial G-action, any G-equivariant
map 𝒫 → 𝒫′ factors uniquely through the projection 𝒫 → 𝒫/G". The functor is built
from chosen per-object quotients (choice + [GHB3]-uniqueness gives functoriality —
the `simulRepresentableBy` construction pattern of T-Q6c); the geometric clauses come
from the torsor property ([GHB4]) and splitting of finite étale covers over `k̄`. -/
theorem exists_quotientProblemData {Q : ModuliProblem R} {G : Type*} [Group G]
    [Finite G] (φ : G →* Aut Q) (hfree : FreeAction φ)
    (hdata : ∀ X : EllObj R, Nonempty (EquivariantRelRepData φ X)) :
    Nonempty (QuotientProblemData φ) := by
  sorry

end ModuliProblem

open EllipticCurve in
/-- **[GH2-core] (freeness of the `GL₂(ℤ/N)`-action on full level structures)** Over a
nonempty base with `N` invertible, a matrix `g` fixing a naive full level structure `L` is the
identity. At a geometric point `L` pins a basis of `E[N] ≅ (ℤ/N)²`
(`torsion_geometricFibre_rank_two`) together with the full-level surjectivity (`L.2.2`); the
resulting finite endomorphism `c ↦ (c 0)•P + (c 1)•Q` is surjective, hence injective
(`Finite.injective_iff_surjective_of_equiv`), so `g` fixes the basis and equals `1`. The
route-independent, `GH1`-free engine of `gammaFullNaive_freeAction` ([GH2]) and the
orbit-distinctness of `gammaHNaiveProblem_not_relativelyRepresentable` ([GHC4]). -/
theorem glSmul_eq_one_of_eq_self {R : CommRingCat.{u}} (N : ℕ) [NeZero N]
    (hinv : IsUnit ((N : ℕ) : R)) (X : EllObj R) (hne : Nonempty X.base)
    (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) (L : X.curve.FullLevelPt N)
    (hfix : X.curve.glSmul g L = L) : g = 1 := by
  -- `N = 1`: `GL₂(ℤ/1)` is trivial.
  rcases eq_or_ne N 1 with rfl | hN1
  · exact Subsingleton.elim _ _
  have hN2 : 2 ≤ N := by have := NeZero.ne N; omega
  haveI : Fact (1 < N) := ⟨by omega⟩
  -- Section equations from `(glSmul g L).1 = L.1`.
  have h1 := congrArg (fun z => z.1.1) hfix
  have h2 := congrArg (fun z => z.1.2) hfix
  simp only [ModularCurves.EllipticCurve.glSmul] at h1 h2
  set m : Matrix (Fin 2) (Fin 2) (ZMod N) := (g : Matrix (Fin 2) (Fin 2) (ZMod N)) with hm
  -- Geometric point.
  obtain ⟨k, fk, ak, t, hk⟩ := EllObj.exists_geometricPoint R X hne N hinv
  letI := fk; letI := ak
  set pp := Point.pull X.curve t L.1.1 with hpp
  set pq := Point.pull X.curve t L.1.2 with hpq
  have hppN : (N : ℤ) • pp = 0 := by rw [hpp, ← Point.pull_zsmul, L.2.1.1, Point.pull_zero]
  have hpqN : (N : ℤ) • pq = 0 := by rw [hpq, ← Point.pull_zsmul, L.2.1.2, Point.pull_zero]
  -- Pull the section equations to `t`.
  have hi : ((m 0 0).val : ℤ) • pp + ((m 1 0).val : ℤ) • pq = pp := by
    have := congrArg (Point.pull X.curve t) h1
    rwa [Point.pull_add, Point.pull_zsmul, Point.pull_zsmul, ← hpp, ← hpq] at this
  have hii : ((m 0 1).val : ℤ) • pp + ((m 1 1).val : ℤ) • pq = pq := by
    have := congrArg (Point.pull X.curve t) h2
    rwa [Point.pull_add, Point.pull_zsmul, Point.pull_zsmul, ← hpp, ← hpq] at this
  -- The rank-two basis at the geometric point, and the torsion submodule.
  obtain ⟨e⟩ := X.curve.torsion_geometricFibre_rank_two N k t hk
  set M := Submodule.torsionBy ℤ (X.curve.Point t) (N : ℤ) with hMdef
  have hppM : pp ∈ M := (Submodule.mem_torsionBy_iff _ _).mpr hppN
  have hpqM : pq ∈ M := (Submodule.mem_torsionBy_iff _ _).mpr hpqN
  -- The candidate map `S c = (c 0).val • pp + (c 1).val • pq : M`.
  have hmem : ∀ c : Fin 2 → ZMod N,
      ((c 0).val : ℤ) • pp + ((c 1).val : ℤ) • pq ∈ M := fun c =>
    add_mem (M.smul_mem _ hppM) (M.smul_mem _ hpqM)
  set S : (Fin 2 → ZMod N) → M :=
    fun c => ⟨((c 0).val : ℤ) • pp + ((c 1).val : ℤ) • pq, hmem c⟩ with hS
  -- Surjectivity of `S` from the full-level condition.
  have hSsurj : Function.Surjective S := by
    intro w
    have hwmem : (w : X.curve.Point t) ∈ AddSubgroup.closure {pp, pq} := by
      have hwN : (N : ℤ) • (w : X.curve.Point t) = 0 := by
        have := w.2; rwa [Submodule.mem_torsionBy_iff] at this
      exact L.2.2 k t (w : X.curve.Point t) hwN
    rw [AddSubgroup.mem_closure_pair] at hwmem
    obtain ⟨j, l, hjl⟩ := hwmem
    refine ⟨![(j : ZMod N), (l : ZMod N)], ?_⟩
    apply Subtype.ext
    simp only [hS, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [zsmul_eq_of_intCast_eq pp hppN (a := (((j : ZMod N)).val : ℤ)) (b := j)
          (by simp [ZMod.natCast_val]),
        zsmul_eq_of_intCast_eq pq hpqN (a := (((l : ZMod N)).val : ℤ)) (b := l)
          (by simp [ZMod.natCast_val])]
    exact hjl
  -- Injectivity via the finite equiv `e`.
  have hSinj : Function.Injective S :=
    (Finite.injective_iff_surjective_of_equiv e.symm.toEquiv).mpr hSsurj
  -- `S ![m00, m10] = ⟨pp,_⟩` and `S ![1,0] = ⟨pp,_⟩`; likewise the second column.
  have hcol1 : S ![m 0 0, m 1 0] = ⟨pp, hppM⟩ := by
    apply Subtype.ext
    simpa only [hS, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using hi
  have hcol2 : S ![m 0 1, m 1 1] = ⟨pq, hpqM⟩ := by
    apply Subtype.ext
    simpa only [hS, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using hii
  have hval1 : ((1 : ZMod N).val : ℤ) = 1 := by simp [ZMod.val_one]
  have hval0 : ((0 : ZMod N).val : ℤ) = 0 := by simp
  have hbase1 : S ![1, 0] = ⟨pp, hppM⟩ := by
    apply Subtype.ext
    simp only [hS, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hval1, hval0,
      one_zsmul, zero_zsmul, add_zero]
  have hbase2 : S ![0, 1] = ⟨pq, hpqM⟩ := by
    apply Subtype.ext
    simp only [hS, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hval1, hval0,
      one_zsmul, zero_zsmul, zero_add]
  -- Injectivity forces the columns.
  have heq1 : (![m 0 0, m 1 0] : Fin 2 → ZMod N) = ![1, 0] := hSinj (hcol1.trans hbase1.symm)
  have heq2 : (![m 0 1, m 1 1] : Fin 2 → ZMod N) = ![0, 1] := hSinj (hcol2.trans hbase2.symm)
  have e00 : m 0 0 = 1 := by have := congrFun heq1 0; simpa using this
  have e10 : m 1 0 = 0 := by have := congrFun heq1 1; simpa using this
  have e01 : m 0 1 = 0 := by have := congrFun heq2 0; simpa using this
  have e11 : m 1 1 = 1 := by have := congrFun heq2 1; simpa using this
  -- Conclude `g = 1`.
  apply Units.ext
  rw [Units.val_one, ← hm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, e00, e10, e01, e11]

/-! ### PART 0 (instantiation) — the `H`-action on the naive full-level problem -/

section GammaH

variable (R : CommRingCat.{u})

/-- **[GH1 = DS-GH1, DATA-SORRY] (Loeffler Fact 3.8.1; KM 7.1.1)** The `H`-action on
the naive full-level problem: `γ` acts on values by `glSmul (γ⁻¹)` (the inverse
because `glSmul_mul` is a RIGHT action law — the 2026-07-06 adversarial fix in
`Moduli/GammaH.lean` — while `Aut`-valued homomorphisms are left actions). Naturality
of the components is KM's diagram 7.1.1.1 = compatibility of `glSmul` with
`pullSection` = the same content as the T-H3 sorries inside `gammaHNaiveProblem.map`;
gate [T-E4a] (`EllHom.pullSection_add`, parked behind T-W7.8; the locally-noetherian
version is PROVEN in `Moduli/PullSectionAdd.lean`). Consumers use only this def and
its spec `gammaHAut_app_val`. -/
noncomputable def gammaHAut (N : ℕ) [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N))) :
    ↥H →* Aut (gammaFullNaiveProblem R N) :=
  sorry

/-- **[GH1, specification]** The value pin of `gammaHAut`: `γ` acts by
`glSmul (γ⁻¹ : GL₂(ℤ/N))`. (Both this and the def discharge together; the pin is what
[GHC3]'s `Quotient.lift` and [GH2]'s freeness argument consume.) -/
theorem gammaHAut_app_val (N : ℕ) [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N))) (γ : ↥H)
    (X : EllObj R) (L : (gammaFullNaiveProblem R N).obj (Opposite.op X)) :
    (gammaHAut R N H γ).hom.app (Opposite.op X) L =
      X.curve.glSmul ((γ⁻¹ : ↥H) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) L := by
  sorry

/-- **[GH2] (KM 7.1.3(2)'s hypothesis for `H ≤ GL₂(ℤ/N)`)** The `H`-action on naive
full level structures is free over nonempty bases when `N` is invertible: a fixed
structure pins a basis of `E[N](k̄) ≅ (ℤ/N)²` at a geometric point
(`EllObj.exists_geometricPoint` + `torsion_geometricFibre_rank_two`, both PROVEN), and
a `GL₂(ℤ/N)`-matrix fixing a basis is `1`. Fails without `hinv` (char `p ∣ N` fibres
have small `E[N]`) and without the nonempty-base guard — both correctly carried. -/
theorem gammaFullNaive_freeAction (N : ℕ) [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hinv : IsUnit (N : R)) :
    ModuliProblem.FreeAction (gammaHAut R N H) := by
  intro X hne γ hγ a hfix
  rw [gammaHAut_app_val] at hfix
  apply hγ
  have hg1 : ((γ⁻¹ : ↥H) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) = 1 :=
    glSmul_eq_one_of_eq_self N hinv X hne _ a hfix
  have hinv1 : (γ⁻¹ : ↥H) = 1 := by
    apply Subtype.ext
    rw [hg1, OneMemClass.coe_one]
  rwa [inv_eq_one] at hinv1

end GammaH

/-! ### PART A — H = 1: Loeffler's "explicit S-scheme", in-repo the T-D18/T-W8 level
scheme

Loeffler 3.8.2 proof, first sentence (verbatim): "For H = {1}, for E/S ∈
Ob(Ell/ℤ[1/N]), we can find an explicit S-scheme representing P_H on Sch/S; it is an
open subscheme of E[N] ×_S E[N] given by non-vanishing of Weil pairings." KM analogue
(THEOREM 3.7.1, verbatim): "Let N ≥ 1 be an integer, S a scheme on which N is
invertible …. Consider the four functors on (Sch/S) given by T ↦ {Γ(N)-structures on
E_T/T, …}. Each is represented by a finite etale S-scheme." The project's explicit
scheme is `levelSpaceΓ E N` (T-D18's Drinfeld incidence locus, closed in
`E[N] ×_S E[N]`, with classifying property `levelSpaceΓ_spec`); over `ℤ[1/N]` it is
also OPEN — Loeffler's Weil-pairing locus — which is exactly the étale conjunct. -/

section PartA

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- **[GHA1]** The structure morphism of the full-level scheme:
`U_{Γ(N)} ↪ E[N] ×_S E[N] → S`. -/
noncomputable def levelSpaceΓπ (N : ℕ) [NeZero N] : levelSpaceΓ E N ⟶ S :=
  levelSpaceΓι E N ≫ pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N

/-- **[GHA2] (finiteness half of KM 3.7.1's conclusion)** `U_{Γ(N)} → S` is finite:
closed immersion (`subschemeι`) into `E[N] ×_S E[N]`, which is finite over `S`
(`torsionπ_isFinite`, T-B4 registered box, + base-change/composition stability).
No invertibility needed. -/
theorem levelSpaceΓπ_isFinite (N : ℕ) [NeZero N] : IsFinite (levelSpaceΓπ E N) := by
  show IsFinite (levelSpaceΓι E N ≫
    pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N)
  have hι : IsFinite (levelSpaceΓι E N) := by
    have h : IsClosedImmersion (levelSpaceΓι E N) :=
      inferInstanceAs (IsClosedImmersion (Scheme.IdealSheafData.subschemeι _))
    infer_instance
  have hπ : IsFinite (E.torsionπ N) := E.torsionπ_isFinite N
  have hfst : IsFinite (pullback.fst (E.torsionπ N) (E.torsionπ N)) :=
    MorphismProperty.pullback_fst _ _ hπ
  infer_instance

/-- **[GHA3] (THE WEIL-PAIRING LEAF — gate [DS4/T-C1], CHARTER-P2)** For `N`
invertible, `U_{Γ(N)} → S` is étale. Loeffler (verbatim): "it is an open subscheme of
E[N] ×_S E[N] given by non-vanishing of Weil pairings" — i.e. `levelSpaceΓ` is the
preimage under `weilPairing` (DS4) of the *primitive* locus `μ_N^× ⊆ μ_N` (for
non-prime `N`, primitivity, not mere non-vanishing), which is clopen over `ℤ[1/N]`;
a clopen subscheme of the finite étale `E[N] ×_S E[N]` (`torsionπ_etale`, T-B5′,
PROVEN) is finite étale over `S`. Unramifiedness is free (closed immersion into
étale); openness/flatness is the genuine content — a closed subscheme of a finite
étale scheme is NOT étale in general. Fallback route (KM 3.7.1's proof, verbatim):
"Because N is invertible on S, the group-scheme E[N] is finite etale over S, locally
(etale) isomorphic to (ℤ/Nℤ)² (cf. 2.3.1). The assertion for Γ(N) … results
immediately from 1.6.7" — étale-local trivialisation + clopen-ness of the condition
on the constant form + descent. -/
theorem levelSpaceΓπ_etale (N : ℕ) [NeZero N] (h : NIsInvertible S N) :
    Etale (levelSpaceΓπ E N) := by
  sorry

end PartA

section PartAModuli

variable (R : CommRingCat.{u})

/-- **[GHA4] (H = 1 relative representability — Loeffler 3.8.2 first sentence; KM
3.7.1 for Γ(N))** For `N` invertible in `R`, the naive full-level problem has, at
every `X : EllObj R`, a relative representation datum with finite étale structure map
— the level scheme `levelSpaceΓ X.curve N` with `levelSpaceΓπ`. The equivalence chain:
`{h : T → U_{Γ(N)} over S} ≃` killed point pairs that are Drinfeld-full-level
(`levelSpaceΓ_spec`, PROVEN modulo registered boxes) `≃` naive full level structures
on `E ×_S T` (`isFullLevel_iff_naive`, T-D8, `NIsInvertible` transported from `hinv`
along `g ≫ X.structMap`; `asSection`/`Section`-of-base-change dictionary). The `nat`
field is genuinely new work (`levelSpaceΓ_spec` is a per-`t` iff): `pullback.lift`
uniqueness against `pullbackAlongMap` functoriality. -/
theorem gammaFullNaive_relRepData (N : ℕ) [NeZero N] (hinv : IsUnit (N : R))
    (X : EllObj R) :
    ∃ d : ModuliProblem.RelRepData (gammaFullNaiveProblem R N) X,
      IsFinite d.f ∧ Etale d.f := by
  obtain ⟨eqv, hnat⟩ := YFull.exists_pointsEquiv_family R X N hinv
  refine ⟨⟨YFull.fullLevelSpace X N, YFull.fullLevelSpaceStruct X N, @eqv, @hnat⟩,
    YFull.isFinite_fullLevelSpaceStruct X N, ?_⟩
  exact levelSpaceΓπ_etale X.curve N (YFull.nIsInvertible_over_spec R X.structMap hinv)

/-- **[GHA5] (H = 1 data, equivariantly)** Upgrade of [GHA4] along the generic
transport [GHB1]: the full-level relative data carries the `gammaHAut`-action. -/
theorem gammaFullNaive_equivariantRelRepData (N : ℕ) [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hinv : IsUnit (N : R)) (X : EllObj R) :
    Nonempty (ModuliProblem.EquivariantRelRepData (gammaHAut R N H) X) := by
  sorry

end PartAModuli

/-! ### PART C — Γ_H: the corrected T-H4/T-H6, bridges to the held declarations, and
the refutation of record -/

section PartC

variable (R : CommRingCat.{u})

/-- **[GHC1] = T-H4 CORRECTED (Loeffler Prop 3.8.2, both sentences; KM 3.7.1 + 7.1.3)**
For `N` invertible in `R` and any `H ≤ GL₂(ℤ/N)`, the quotient problem
`P_H = [Γ(N)]/H` exists with all its KM 7.1.2/7.1.3 properties: relatively
representable by finite étale morphisms, couniversal, and with
`P_H(E/k̄) = {H-orbits of full level structures}` (Loeffler Fact 3.8.1, via the
`geom_*` clauses). Assembly of [GHA5] + [GH2] + [GHB7]. This replaces the held
`gammaHNaive_relativelyRepresentable` (GammaH.lean:432), which is FALSE for `H ≠ ⊥`
([GHC4]); the two statements agree exactly at `H = ⊥` ([GHC2]). -/
theorem gammaH_relativelyRepresentable (N : ℕ) [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hinv : IsUnit (N : R)) :
    Nonempty (ModuliProblem.QuotientProblemData (gammaHAut R N H)) := by
  sorry

/-- **[GHC2] (bridge — the held T-H4 statement IS true at `H = ⊥`, and this discharges
it there)** The full conclusion of the held `gammaHNaive_relativelyRepresentable`
specialised to `H = ⊥`: `⊥`-orbits are singletons (`gammaHNaive_bot`, held file,
PROVEN), so the naive problem at `⊥` is isomorphic to `gammaFullNaiveProblem` and
[GHA4] supplies both conjuncts (transport of `RelativelyRepresentable` and of the
existential conjunct across a functor isomorphism). -/
theorem gammaHNaive_relativelyRepresentable_bot (N : ℕ) [NeZero N]
    (hinv : IsUnit (N : R)) :
    (gammaHNaiveProblem R N ⊥).RelativelyRepresentable ∧
      ∀ X : EllObj R, ∃ (Z : Scheme.{u}) (f : Z ⟶ X.base), IsFinite f ∧ Etale f ∧
        ∀ {T : Scheme.{u}} (g : T ⟶ X.base), Nonempty
          ({ h : T ⟶ Z // h ≫ f = g } ≃
            (gammaHNaiveProblem R N ⊥).obj (Opposite.op (X.pullbackAlong g))) := by
  sorry

/-- **[GHC3] (bridge = Loeffler Fact 3.8.1 as a theorem)** The naive orbit problem
maps to the quotient problem — `pkg.proj` descends through the global-orbit quotient
(well-defined by `proj_invariant` + the `gammaHAut_app_val` pin) — and the comparison
is bijective at every object over `Spec k̄` (verbatim: "if k̄ is algebraically closed
… P_H(E/k̄) = {H-orbits of isomorphisms (ℤ/N)² ≅ E[N]}"; the mechanism is Loeffler
§3.6's, verbatim: "In general, this is neither injective nor surjective, but if
S = Spec(k̄) … bijective"). NOT an isomorphism of problems for `H ≠ ⊥` — [GHC4]. -/
theorem gammaHNaive_toQuotient (N : ℕ) [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (pkg : ModuliProblem.QuotientProblemData (gammaHAut R N H)) :
    ∃ θ : gammaHNaiveProblem R N H ⟶ pkg.prob,
      (∀ (X : EllObj R) (L : X.curve.FullLevelPt N),
        θ.app (Opposite.op X) (Quotient.mk (X.curve.hOrbitSetoid H) L) =
          pkg.proj.app (Opposite.op X) L) ∧
      ∀ (k : Type u) [Field k] [IsAlgClosed k]
        (sm : Spec (CommRingCat.of k) ⟶ Spec R)
        (E : EllipticCurve (Spec (CommRingCat.of k))),
        Function.Bijective
          (θ.app (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R))) := by
  sorry

/-- **[GHC4] (THE REFUTATION OF RECORD — adversarial finding F1, B2 statement event)**
For `H ≠ ⊥`, the naive global-orbit problem `gammaHNaiveProblem R N H` is NOT
relatively representable, given any witness object with a nonempty base and a naive
full level structure (such witnesses exist over every nontrivial `R` with `N`
invertible — e.g. the tautological point over the level scheme). Route: over
`T = X.base ⨿ X.base` the classes `[(L, L)]` and `[(L, γ·L)]` (`γ ∈ H`, `γ ≠ 1`) are
distinct — the `H`-action is free over nonempty bases ([GH2]'s core argument) — yet
restrict equally to both components, while a representable functor separates points by
their restrictions to the components of a coproduct (`RelativelyRepresentable`'s
naturality clause + gluing of morphisms). This refutes the held
`gammaHNaive_relativelyRepresentable` (GammaH.lean:432) for every `H ≠ ⊥`; the held
T-H6 (GammaH.lean:460) inherits the defect (its conclusion asserts `.Representable`
of the same functor). Supersedes the 2026-07-06 levels-stack attack verdict
"[FALSITY] TRUE". -/
theorem gammaHNaiveProblem_not_relativelyRepresentable (N : ℕ) [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N))) (hH : H ≠ ⊥)
    (hinv : IsUnit (N : R)) (X : EllObj R) (hne : Nonempty X.base)
    (L : (gammaFullNaiveProblem R N).obj (Opposite.op X)) :
    ¬ (gammaHNaiveProblem R N H).RelativelyRepresentable := by
  sorry

/-- **[GHC5] (KM 4.7.1's hypothesis shape: "affine and etale over (Ell)")** A quotient
problem package is affine over `Ell`: finite morphisms are affine, so `relRep`
repackages into `AffineOverEll` (the KM SCHOLIE 4.7.0 hypothesis, v10.27/B2 amendment
of record). Feeds `representable_iff`. -/
theorem ModuliProblem.QuotientProblemData.affineOverEll {Q : ModuliProblem R}
    {G : Type*} [Group G] [Finite G] {φ : G →* Aut Q}
    (pkg : ModuliProblem.QuotientProblemData φ) :
    pkg.prob.AffineOverEll := by
  sorry

/-- **[GHC6] = T-H6 CORRECTED, route (gate [T-E5-engine])** — KM COROLLARY 4.7.1
(verbatim): "Any relatively representable moduli problem 𝒫 which is affine and etale
over (Ell), and rigid, is representable by a smooth affine curve over ℤ"; KM 4.7.2
(verbatim): "For N ≥ 3, the naive level N moduli problems of 4.6 is representable, by
a smooth affine curve Y(N) over ℤ[1/N]. Proof. This results from 4.7.1 above, thanks
to the rigidity 2.7.2 and the relative representability 3.7.1 of naive level N
structures." Here: the representability conclusion for the quotient problem `P_H`,
via [GHC5] + `representable_iff` (T-E5; its ⇐ is the T-Q6e-gated engine). The
smooth-affine-*base* conjunct of the held T-H6 is deliberately NOT reproduced (KM
4.7.1's smoothness argument is the separate future cut [GH-SMOOTH]); the rigidity
hypothesis is stated for the quotient problem — the transfer from the naive problem's
rigidity (T-H5's criterion) is the future cut [GH-RIGID-XFER], consuming [GHC3]. -/
theorem gammaH_representable_of_rigid (N : ℕ) [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hinv : IsUnit (N : R))
    (pkg : ModuliProblem.QuotientProblemData (gammaHAut R N H))
    (hrig : pkg.prob.Rigid) :
    pkg.prob.Representable := by
  sorry

end PartC

end ModularCurves
