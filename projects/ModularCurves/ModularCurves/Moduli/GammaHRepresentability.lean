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
import ModularCurves.GroupScheme.DeligneOrder
import ModularCurves.Moduli.NaiveProblems

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
  /-- The representing bijections are `G`-equivariant (diagram KM 7.1.1.1). The `γ⁻¹`
  twist is forced by rigour: the classifying transport `γ ↦ classify(φ γ)` is
  *anti*-homomorphic (Yoneda is contravariant), so a genuine `SchemeAction`
  homomorphism (`SchemeAction.ofAut`, via `(·).inv`) realizes `σZ.hom γ` as
  `classify((φ γ)⁻¹) = classify(φ γ⁻¹)`; consumers see the inverse and reindex freely
  (`FreeAction` is invariant under `γ ↦ γ⁻¹`). -/
  equivariant : ∀ {T : Scheme.{u}} (g : T ⟶ X.base)
    (h : { h : T ⟶ Z // h ≫ f = g }) (γ : G),
    eqv g ⟨h.1 ≫ σZ.hom γ, by rw [Category.assoc, over_base, h.2]⟩ =
      (φ γ⁻¹).hom.app (Opposite.op (X.pullbackAlong g)) (eqv g h)
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
  -- The universal element.
  set univ := d.eqv d.f ⟨𝟙 d.Z, Category.id_comp d.f⟩ with huniv
  -- Relative `transportHom`: for `η : Q ⟶ Q`, the over-`f` endo of `Z` classifying `η(univ)`.
  set rT : (Q ⟶ Q) → { s : d.Z ⟶ d.Z // s ≫ d.f = d.f } :=
    fun η => (d.eqv d.f).symm (η.app _ univ) with hrT
  have hrTspec : ∀ η : Q ⟶ Q, d.eqv d.f (rT η) = η.app _ univ := by
    intro η; rw [hrT]; exact (d.eqv d.f).apply_symm_apply _
  -- Reconstruction: any classifying map pulls the universal element.
  have recon : ∀ {T : Scheme.{u}} (k : T ⟶ d.Z),
      d.eqv (k ≫ d.f) ⟨k, rfl⟩ = Q.map (X.pullbackAlongMap d.f k).op univ := by
    intro T k
    have hnat := d.nat d.f k ⟨𝟙 d.Z, Category.id_comp d.f⟩
    simp only [Category.comp_id] at hnat
    rw [huniv, ← hnat]
  -- The characterizing property (relative `homEquiv_comp_transportHom`).
  have relKey : ∀ {T : Scheme.{u}} (g : T ⟶ X.base) (v1 : T ⟶ d.Z)
      (hv : v1 ≫ d.f = g) (η : Q ⟶ Q),
      d.eqv g ⟨v1 ≫ (rT η).1, by rw [Category.assoc, (rT η).2, hv]⟩
        = η.app _ (d.eqv g ⟨v1, hv⟩) := by
    intro T g v1 hv η
    subst hv
    have hnat := d.nat d.f v1 (rT η)
    rw [hrTspec] at hnat
    rw [hnat, ← NatTrans.naturality_apply η (X.pullbackAlongMap d.f v1).op univ, ← recon v1]
  -- `rT` sends the identity to the identity.
  have hidT : (rT (𝟙 Q)).1 = 𝟙 d.Z := by
    have h := hrTspec (𝟙 Q)
    simp only [NatTrans.id_app, types_id_apply] at h
    rw [huniv] at h
    exact congrArg Subtype.val ((d.eqv d.f).injective h)
  -- `rT` is multiplicative (covariant in composition).
  have hcompT : ∀ η θ : Q ⟶ Q, (rT (η ≫ θ)).1 = (rT η).1 ≫ (rT θ).1 := by
    intro η θ
    have key : d.eqv d.f (rT (η ≫ θ))
        = d.eqv d.f ⟨(rT η).1 ≫ (rT θ).1,
            by rw [Category.assoc, (rT θ).2, (rT η).2]⟩ := by
      rw [hrTspec, relKey d.f (rT η).1 (rT η).2 θ,
        show (⟨(rT η).1, (rT η).2⟩ : { s : d.Z ⟶ d.Z // s ≫ d.f = d.f }) = rT η from rfl,
        hrTspec η]
      rfl
    exact congrArg Subtype.val ((d.eqv d.f).injective key)
  refine ⟨{
    toRelRepData := d
    σZ :=
      { hom := fun γ => (rT ((φ γ).inv)).1
        hom_one := by
          show (rT ((φ (1 : G)).inv)).1 = 𝟙 d.Z
          rw [show (φ (1 : G)).inv = 𝟙 Q from by rw [map_one]; rfl, hidT]
        hom_mul := fun γ₁ γ₂ => by
          show (rT ((φ (γ₁ * γ₂)).inv)).1
            = (rT ((φ γ₁).inv)).1 ≫ (rT ((φ γ₂).inv)).1
          rw [show (φ (γ₁ * γ₂)).inv = (φ γ₁).inv ≫ (φ γ₂).inv from by rw [map_mul]; rfl,
            hcompT] }
    over_base := fun γ => (rT ((φ γ).inv)).2
    equivariant := by
      intro T g h γ
      show d.eqv g ⟨h.1 ≫ (rT ((φ γ).inv)).1, _⟩ = (φ γ⁻¹).hom.app _ (d.eqv g h)
      rw [show (φ γ⁻¹).hom = (φ γ).inv from by rw [map_inv]; rfl]
      exact relKey g h.1 h.2 ((φ γ).inv)
    finite := hfin
    etale := het }⟩

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
absent, cut [GH-DESC-GAP]).

**[GH-DESC-GAP] CONFIRMED (gap-check, NEW-GH 2026-07-09).** This *abstract* statement —
descend the SECOND factor `f₀` of `π ≫ f₀` along the surjective finite-étale source-cover
`π` — is NOT provided by the current mathlib pin. What exists: `IsFinite.of_comp` /
`Etale.of_comp` and `HasOfPostcompProperty @IsFinite @IsSeparated` / `@Etale @Etale` cancel
the FIRST factor (wrong factor here); the `MorphismProperty.DescendsAlong _ (@Surjective ⊓
@Flat ⊓ @QuasiCompact)` instances are BASE-CHANGE descent (covers of the base `S`, not the
source-cover `π`) and cover only `UniversallyClosed/Open/Injective`, `isomorphisms`,
`IsOpenImmersion`, `Surjective` — not `@IsFinite`/`@Etale`. No `HasOfPrecompProperty` and no
fppf source-descent for finite/étale. Discharging this abstractly = a from-scratch
ForMathlib fppf/finite-locally-free descent development (`ForMathlib/FiniteEtaleDescent.lean`),
which is out of scope for a "NOW" leaf (v10.24: decompose-don't-grind). **Intended
discharge for the Y(N) pipeline is the PRIMARY chart-local route above** — provable in the
GHB4/GHB7 quotient context where `Aᴳ ⊆ A` is a projective (hence flat, direct-summand)
`B`-submodule of the finite `B`-module `A`; it does NOT need this abstract lemma. Left
gated pending either. -/
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
    simp only [hS, Matrix.cons_val_zero, Matrix.cons_val_one]
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
    simp only [hS, Matrix.cons_val_zero, Matrix.cons_val_one, hval1, hval0,
      one_zsmul, zero_zsmul, add_zero]
  have hbase2 : S ![0, 1] = ⟨pq, hpqM⟩ := by
    apply Subtype.ext
    simp only [hS, Matrix.cons_val_zero, Matrix.cons_val_one, hval1, hval0,
      one_zsmul, zero_zsmul, zero_add]
  -- Injectivity forces the columns.
  have heq1 : (![m 0 0, m 1 0] : Fin 2 → ZMod N) = ![1, 0] := hSinj (hcol1.trans hbase1.symm)
  have heq2 : (![m 0 1, m 1 1] : Fin 2 → ZMod N) = ![0, 1] := hSinj (hcol2.trans hbase2.symm)
  have e00 : m 0 0 = 1 := by simpa using congrFun heq1 0
  have e10 : m 1 0 = 0 := by simpa using congrFun heq1 1
  have e01 : m 0 1 = 0 := by simpa using congrFun heq2 0
  have e11 : m 1 1 = 1 := by simpa using congrFun heq2 1
  -- Conclude `g = 1`.
  apply Units.ext
  rw [Units.val_one, ← hm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e00, e10, e01, e11]

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

set_option backward.isDefEq.respectTransparency false in
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
a clopen subscheme of the finite étale `E[N] ×_S E[N]` (`Torsionπ.etale`, T-B5′,
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
    YFull.isFinite_fullLevelSpaceStruct X N
      (YFull.nIsInvertible_over_spec R X.structMap hinv), ?_⟩
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

/-- Relative representability transports across a functor isomorphism of moduli problems:
the representing datum `(Z, f)` is reused and the classifying bijections are post-composed
with the iso's components; the naturality clause carries by naturality of `e.inv`. -/
theorem ModuliProblem.relativelyRepresentable_of_iso {R : CommRingCat.{u}}
    {P Q : ModuliProblem R} (e : P ≅ Q)
    (hQ : Q.RelativelyRepresentable) : P.RelativelyRepresentable := by
  intro X
  obtain ⟨Z, f, eqv, nat⟩ := hQ X
  refine ⟨Z, f, fun {T} g =>
    (eqv g).trans (e.app (Opposite.op (X.pullbackAlong g))).toEquiv.symm, ?_⟩
  intro T T' g k h
  simp only [Equiv.trans_apply]
  rw [nat]
  exact NatTrans.naturality_apply e.inv (X.pullbackAlongMap g k).op (eqv g h)

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
  obtain ⟨e⟩ := gammaHNaive_bot R N
  have hQ : (gammaFullNaiveProblem R N).RelativelyRepresentable :=
    (ModuliProblem.relativelyRepresentable_iff_nonempty_relRepData _).mpr
      (fun Y => ⟨(gammaFullNaive_relRepData R N hinv Y).choose⟩)
  refine ⟨ModuliProblem.relativelyRepresentable_of_iso e hQ, fun X => ?_⟩
  obtain ⟨d, hfin, het⟩ := gammaFullNaive_relRepData R N hinv X
  exact ⟨d.Z, d.f, hfin, het, fun {T} g => ⟨(d.eqv g).trans
    (e.app (Opposite.op (X.pullbackAlong g))).toEquiv.symm⟩⟩

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

/-- Restriction of a point is `ℤ`-linear, derived from additivity (`restrict_add`)
via `map_zsmul`. Companion to `Point.restrict_add`/`restrict_zero`
(`GroupScheme/DeligneOrder.lean`); needed by the coproduct-glue construction of the
`gammaHNaiveProblem` refutation. -/
theorem EllipticCurve.Point.restrict_zsmul {S : Scheme.{u}} (E : EllipticCurve S)
    {T T' : Scheme.{u}} {g : T ⟶ S} (k : T' ⟶ T) (n : ℤ) (P : E.Point g) :
    EllipticCurve.Point.restrict E k (n • P) = n • EllipticCurve.Point.restrict E k P :=
  map_zsmul (AddMonoidHom.mk' (EllipticCurve.Point.restrict E k)
    (EllipticCurve.Point.restrict_add E k)) n P

/-- Glue a `Bool`-family of sections of `X.curve` into a `T`-point over `g`, where
`T = ∐Bool` and `g` restricts to `𝟙` on each summand (the section-level content of
the coproduct-glue that produces the second, distinct global orbit in the GHC4
refutation). -/
noncomputable def coprodPoint {R : CommRingCat.{u}} (X : EllObj R)
    (g : (∐ fun _ : Bool => X.base) ⟶ X.base)
    (hg : ∀ b : Bool, Sigma.ι (fun _ : Bool => X.base) b ≫ g = 𝟙 X.base)
    (s : Bool → X.curve.Section) : X.curve.Point g :=
  ⟨Sigma.desc (fun b => (s b).1), by
    refine Sigma.hom_ext _ _ (fun b => ?_)
    rw [← Category.assoc, Sigma.ι_desc, (s b).2, hg b]⟩

lemma coprodPoint_ι {R : CommRingCat.{u}} (X : EllObj R)
    (g : (∐ fun _ : Bool => X.base) ⟶ X.base)
    (hg : ∀ b : Bool, Sigma.ι (fun _ : Bool => X.base) b ≫ g = 𝟙 X.base)
    (s : Bool → X.curve.Section) (b : Bool) :
    Sigma.ι (fun _ : Bool => X.base) b ≫ (coprodPoint X g hg s).1 = (s b).1 := by
  simp only [coprodPoint, Sigma.ι_desc]

open EllipticCurve in
/-- The glued point is killed by `N` when each component section is (the killing half
of the coproduct-glue's `IsNaiveFullLevel`). -/
lemma coprodPoint_nsmul_eq_zero {R : CommRingCat.{u}} (X : EllObj R) (N : ℕ)
    (g : (∐ fun _ : Bool => X.base) ⟶ X.base)
    (hg : ∀ b : Bool, Sigma.ι (fun _ : Bool => X.base) b ≫ g = 𝟙 X.base)
    (s : Bool → X.curve.Section) (hs : ∀ b, (N : ℤ) • s b = 0) :
    (N : ℤ) • coprodPoint X g hg s = 0 := by
  refine Subtype.ext (Sigma.hom_ext _ _ (fun b => ?_))
  have hL : Sigma.ι (fun _ : Bool => X.base) b ≫ ((N : ℤ) • coprodPoint X g hg s).1
      = (s b).1 ≫ X.curve.mulByHom N := by
    rw [point_smul_eq_comp_mulBy, ← Category.assoc, coprodPoint_ι]
  have hR0 : Point.restrict X.curve (Sigma.ι (fun _ : Bool => X.base) b)
      (0 : X.curve.Point g) = 0 := Point.restrict_zero X.curve _
  have hRcoe : Sigma.ι (fun _ : Bool => X.base) b ≫ (0 : X.curve.Point g).1
      = (0 : X.curve.Point (Sigma.ι (fun _ : Bool => X.base) b ≫ g)).1 :=
    congrArg Subtype.val hR0
  rw [hL, hRcoe]
  have hsz : ((N : ℤ) • s b).1 = (s b).1 ≫ X.curve.mulByHom N :=
    point_smul_eq_comp_mulBy X.curve _ N (s b)
  rw [← hsz, hs b]
  exact (congrArg (fun h : X.base ⟶ X.base => (0 : X.curve.Point h).1) (hg b)).symm

/-- **[GHC4-SEP] (the separated-presheaf half of the refutation)** A relative
representation datum separates a global value of the represented functor by its
restrictions to the two components of a `Bool`-coproduct base: the injectivity core
of the sheaf condition, packaged from `RelRepData`'s naturality clause (`d.nat`), the
representing bijection's injectivity, and `Sigma.hom_ext`. Axiom-clean; the reusable
engine of `gammaHNaiveProblem_not_relativelyRepresentable`. -/
theorem relRepData_sep_coprod {Q : ModuliProblem R} {X : EllObj R}
    (d : ModuliProblem.RelRepData Q X)
    (g : (∐ fun _ : Bool => X.base) ⟶ X.base)
    (a b : Q.obj (Opposite.op (X.pullbackAlong g)))
    (hres : ∀ i : Bool,
      Q.map (X.pullbackAlongMap g (Sigma.ι (fun _ : Bool => X.base) i)).op a
        = Q.map (X.pullbackAlongMap g (Sigma.ι (fun _ : Bool => X.base) i)).op b) :
    a = b := by
  set va := (d.eqv g).symm a with hva
  set vb := (d.eqv g).symm b with hvb
  have hvae : d.eqv g va = a := (d.eqv g).apply_symm_apply a
  have hvbe : d.eqv g vb = b := (d.eqv g).apply_symm_apply b
  have hcol : ∀ i : Bool,
      Sigma.ι (fun _ : Bool => X.base) i ≫ va.1
        = Sigma.ι (fun _ : Bool => X.base) i ≫ vb.1 := by
    intro i
    have hna := d.nat g (Sigma.ι (fun _ : Bool => X.base) i) va
    have hnb := d.nat g (Sigma.ι (fun _ : Bool => X.base) i) vb
    rw [hvae] at hna
    rw [hvbe] at hnb
    have heq : d.eqv (Sigma.ι (fun _ : Bool => X.base) i ≫ g)
          ⟨Sigma.ι (fun _ : Bool => X.base) i ≫ va.1, by rw [Category.assoc, va.2]⟩
        = d.eqv (Sigma.ι (fun _ : Bool => X.base) i ≫ g)
          ⟨Sigma.ι (fun _ : Bool => X.base) i ≫ vb.1, by rw [Category.assoc, vb.2]⟩ := by
      rw [hna, hnb, hres i]
    exact congrArg Subtype.val ((d.eqv _).injective heq)
  have hv : va.1 = vb.1 := Sigma.hom_ext _ _ hcol
  rw [← hvae, ← hvbe, Subtype.ext hv]

/-- A morphism from `Spec` of a field into a `Bool`-indexed scheme coproduct factors
through one of the two summands: the coproduct's space is the disjoint union of the
summands (`sigmaMk`) and `Spec k` has a single point, so its image lands in one
summand's (open) range and `IsOpenImmersion.lift` produces the factorisation. -/
private lemma spec_factors_coprod {k : Type u} [Field k] (Y : Bool → Scheme.{u})
    (t : Spec (CommRingCat.of k) ⟶ ∐ Y) :
    ∃ (b : Bool) (s : Spec (CommRingCat.of k) ⟶ Y b), s ≫ Sigma.ι Y b = t := by
  obtain ⟨b, y, hby⟩ := (sigmaOpenCover Y).exists_eq (t.base default)
  haveI : IsOpenImmersion (Sigma.ι Y b) := (sigmaOpenCover Y).map_prop b
  have hsub : Set.range t.base ⊆ Set.range (Sigma.ι Y b).base := by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z default]
    exact ⟨y, hby⟩
  exact ⟨b, IsOpenImmersion.lift (Sigma.ι Y b) t hsub,
    IsOpenImmersion.lift_fac (Sigma.ι Y b) t hsub⟩

open EllipticCurve in
/-- `EllHom.pullSection` along the base-change comparison morphism `pullbackAlongMap g k`
restricts the represented point: `pullSection (pullbackAlongMap g k) (asSection g P)
= asSection (k ≫ g) (P.restrict k)`. (Re-statement of the identically-named private
lemma of `ModularCurve/YFullRoute.lean`, needed here for the coproduct-glue restriction
identity `coprodFullLevel_restrict`.) -/
private theorem pullSection_asSection_aux {R : CommRingCat.{u}} (X : EllObj R)
    {T T' : Scheme.{u}} (g : T ⟶ X.base) (k : T' ⟶ T) (P : X.curve.Point g) :
    EllHom.pullSection R (X.pullbackAlongMap g k) (Point.asSection X.curve g P) =
      Point.asSection X.curve (k ≫ g) (Point.restrict X.curve k P) := by
  have htop : (X.pullbackAlongMap g k).top ≫ pullback.fst X.curve.π g =
      pullback.fst X.curve.π (k ≫ g) := by
    show Limits.pullback.map X.curve.π (k ≫ g) X.curve.π g (𝟙 _) k (𝟙 _)
        (by simp) (by simp) ≫ Limits.pullback.fst X.curve.π g =
      Limits.pullback.fst X.curve.π (k ≫ g)
    rw [Limits.pullback.lift_fst, Category.comp_id]
  refine Subtype.ext (pullback.hom_ext ?_ ?_)
  · refine ((congrArg ((EllHom.pullSection R (X.pullbackAlongMap g k)
        (Point.asSection X.curve g P)).1 ≫ ·) htop.symm).trans ?_).trans
      (Point.asSection_val_fst X.curve (k ≫ g) (Point.restrict X.curve k P)).symm
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ pullback.fst X.curve.π g)
      ((X.pullbackAlongMap g k).isPullback.lift_fst _ _ _)).trans ?_
    exact (Category.assoc _ _ _).trans
      (congrArg (k ≫ ·) (Point.asSection_val_fst X.curve g P))
  · exact (EllHom.pullSection R (X.pullbackAlongMap g k)
      (Point.asSection X.curve g P)).2.trans
      (Point.asSection_val_snd X.curve (k ≫ g) (Point.restrict X.curve k P)).symm

open EllipticCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **[GHC4, the glue]** Glue a `Bool`-family of naive full level structures on
`X.curve` into a full level structure on the base change `X.curve.baseChange g`, where
`g` restricts to `𝟙` on each `Bool`-summand. This is the constructor of the "second
global orbit" separating the naive `Γ_H` orbit presheaf: the killing clause is
`coprodPoint_nsmul_eq_zero` (through `asSection`); the fibrewise generation clause
reduces, by factoring a geometric point through one summand (`spec_factors_coprod`), to
that summand's own generation clause (mirroring `isNaiveFullLevel_pullAlong`). -/
noncomputable def coprodFullLevel {R : CommRingCat.{u}} (N : ℕ) [NeZero N] (X : EllObj R)
    (g : (∐ fun _ : Bool => X.base) ⟶ X.base)
    (hg : ∀ b : Bool, Sigma.ι (fun _ : Bool => X.base) b ≫ g = 𝟙 X.base)
    (Lf : Bool → X.curve.FullLevelPt N) :
    (X.curve.baseChange g).FullLevelPt N := by
  have hzero : Point.asSection X.curve g (0 : X.curve.Point g) = 0 := by
    have h0 := Point.asSection_zsmul X.curve g 0 (0 : X.curve.Point g)
    simpa using h0
  refine ⟨(Point.asSection X.curve g (coprodPoint X g hg (fun b => (Lf b).1.1)),
    Point.asSection X.curve g (coprodPoint X g hg (fun b => (Lf b).1.2))), ⟨?_, ?_⟩, ?_⟩
  · rw [← Point.asSection_zsmul,
      coprodPoint_nsmul_eq_zero X N g hg _ (fun b => (Lf b).2.1.1)]
    exact hzero
  · rw [← Point.asSection_zsmul,
      coprodPoint_nsmul_eq_zero X N g hg _ (fun b => (Lf b).2.1.2)]
    exact hzero
  · intro k _ _ t x hx
    obtain ⟨b, s, hs⟩ := spec_factors_coprod (fun _ : Bool => X.base) t
    have htg : t ≫ g = s := by rw [← hs, Category.assoc, hg b, Category.comp_id]
    have hdx : (N : ℤ) • Point.baseChangeEquiv X.curve g t x = 0 := by
      have h1 : Point.baseChangeEquiv X.curve g t ((N : ℤ) • x) =
          (N : ℤ) • Point.baseChangeEquiv X.curve g t x :=
        map_zsmul (Point.baseChangeEquiv X.curve g t).toAddMonoidHom (N : ℤ) x
      rw [← h1, hx]
      exact map_zero (Point.baseChangeEquiv X.curve g t).toAddMonoidHom
    have hcompatP : Point.baseChangeEquiv X.curve g t
        (Point.pull (X.curve.baseChange g) t
          (Point.asSection X.curve g (coprodPoint X g hg (fun b => (Lf b).1.1))))
        = Point.pull X.curve (t ≫ g) (Lf b).1.1 := by
      refine Subtype.ext ?_
      rw [Point.baseChangeEquiv_apply_coe]
      show (t ≫ (Point.asSection X.curve g (coprodPoint X g hg (fun b => (Lf b).1.1))).1)
            ≫ pullback.fst X.curve.π g = (t ≫ g) ≫ (Lf b).1.1.1
      rw [htg, Category.assoc, Point.asSection_val_fst, ← hs, Category.assoc, coprodPoint_ι]
    have hcompatQ : Point.baseChangeEquiv X.curve g t
        (Point.pull (X.curve.baseChange g) t
          (Point.asSection X.curve g (coprodPoint X g hg (fun b => (Lf b).1.2))))
        = Point.pull X.curve (t ≫ g) (Lf b).1.2 := by
      refine Subtype.ext ?_
      rw [Point.baseChangeEquiv_apply_coe]
      show (t ≫ (Point.asSection X.curve g (coprodPoint X g hg (fun b => (Lf b).1.2))).1)
            ≫ pullback.fst X.curve.π g = (t ≫ g) ≫ (Lf b).1.2.1
      rw [htg, Category.assoc, Point.asSection_val_fst, ← hs, Category.assoc, coprodPoint_ι]
    have h1 := (Lf b).2.2 k (t ≫ g) (Point.baseChangeEquiv X.curve g t x) hdx
    rw [← hcompatP, ← hcompatQ] at h1
    have hKle : AddSubgroup.closure
        ({Point.baseChangeEquiv X.curve g t (Point.pull (X.curve.baseChange g) t
            (Point.asSection X.curve g (coprodPoint X g hg (fun b => (Lf b).1.1)))),
          Point.baseChangeEquiv X.curve g t (Point.pull (X.curve.baseChange g) t
            (Point.asSection X.curve g (coprodPoint X g hg (fun b => (Lf b).1.2))))} :
          Set (X.curve.Point (t ≫ g)))
        ≤ (AddSubgroup.closure
            {Point.pull (X.curve.baseChange g) t
                (Point.asSection X.curve g (coprodPoint X g hg (fun b => (Lf b).1.1))),
              Point.pull (X.curve.baseChange g) t
                (Point.asSection X.curve g (coprodPoint X g hg (fun b => (Lf b).1.2)))}).map
          (Point.baseChangeEquiv X.curve g t).toAddMonoidHom := by
      rw [AddSubgroup.closure_le]
      rintro z (rfl | rfl)
      · exact ⟨_, AddSubgroup.subset_closure (Set.mem_insert _ _), rfl⟩
      · exact ⟨_, AddSubgroup.subset_closure (Set.mem_insert_of_mem _ rfl), rfl⟩
    obtain ⟨y, hy, hyx⟩ := hKle h1
    exact ((Point.baseChangeEquiv X.curve g t).injective hyx) ▸ hy

/-- `EllHom.pullSection` is `ℤ`-linear (derived from `pullSection_add` via `map_zsmul`).
Companion to `EllHom.pullSection_add`. -/
theorem EllHom.pullSection_zsmul {R : CommRingCat.{u}} {X Y : EllObj R} (f : X ⟶ Y)
    (n : ℤ) (P : Y.curve.Section) :
    EllHom.pullSection R f (n • P) = n • EllHom.pullSection R f P :=
  map_zsmul (AddMonoidHom.mk' (EllHom.pullSection R f) (EllHom.pullSection_add R f)) n P

open EllipticCurve in
/-- `baseChangeEquiv` undoes `asSection`: `e (asSection g R) = R.restrict (𝟙)`. The
section `asSection E g R` is the pullback-lift of `R` and its image under the base-change
comparison is `R` itself (reindexed along `𝟙 ≫ g`). -/
lemma baseChangeEquiv_asSection {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}
    (g : T ⟶ S) (R : E.Point g) :
    Point.baseChangeEquiv E g (𝟙 T) (Point.asSection E g R) = Point.restrict E (𝟙 T) R := by
  refine Subtype.ext ?_
  rw [Point.baseChangeEquiv_apply_coe, Point.asSection_val_fst]
  show R.1 = 𝟙 T ≫ R.1
  rw [Category.id_comp]

open EllipticCurve in
/-- `Point.asSection` is additive. Proven by transporting through the additive
`baseChangeEquiv` (whose inverse `asSection` is, up to the `𝟙 ≫ g` reindex handled by
`baseChangeEquiv_asSection`) and `Point.restrict_add`. Addition of points has no direct
underlying-morphism formula, so the transport route replaces a `pullback.hom_ext`. -/
theorem Point.asSection_add {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}
    (g : T ⟶ S) (P Q : E.Point g) :
    Point.asSection E g (P + Q) = Point.asSection E g P + Point.asSection E g Q := by
  apply (Point.baseChangeEquiv E g (𝟙 T)).injective
  rw [map_add, baseChangeEquiv_asSection, baseChangeEquiv_asSection, baseChangeEquiv_asSection,
    Point.restrict_add]

open EllipticCurve in
/-- `Point.asSection E g` is injective (compose with the first pullback projection). -/
lemma asSection_injective {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}
    (g : T ⟶ S) : Function.Injective (Point.asSection E g) := by
  intro P Q h
  refine Subtype.ext ?_
  have h1 : (Point.asSection E g P).1 ≫ pullback.fst E.π g
      = (Point.asSection E g Q).1 ≫ pullback.fst E.π g :=
    congrArg (· ≫ pullback.fst E.π g) (congrArg Subtype.val h)
  rwa [Point.asSection_val_fst, Point.asSection_val_fst] at h1

open EllipticCurve in
/-- Restricting the coproduct-glued point to a `Bool`-summand recovers the summand's
section, as a point over `Sigma.ι i ≫ g` (`coprodPoint_ι` + `hg`). -/
lemma restrict_coprodPoint {R : CommRingCat.{u}} (X : EllObj R)
    (g : (∐ fun _ : Bool => X.base) ⟶ X.base)
    (hg : ∀ b : Bool, Sigma.ι (fun _ : Bool => X.base) b ≫ g = 𝟙 X.base)
    (sf : Bool → X.curve.Section) (i : Bool) :
    Point.restrict X.curve (Sigma.ι (fun _ : Bool => X.base) i) (coprodPoint X g hg sf)
      = Point.pull X.curve (Sigma.ι (fun _ : Bool => X.base) i ≫ g) (sf i) := by
  refine Subtype.ext ?_
  show Sigma.ι (fun _ : Bool => X.base) i ≫ (coprodPoint X g hg sf).1
    = (Sigma.ι (fun _ : Bool => X.base) i ≫ g) ≫ (sf i).1
  rw [coprodPoint_ι, hg i, Category.id_comp]

open EllipticCurve in
/-- `FullLevelPt.pullAlong` commutes with the `GL₂`-action: `pullAlong σ (glSmul γ L)
= glSmul γ (pullAlong σ L)`. Both sides are `asSection ∘ pull` of the `glSmul`-combination,
and `pull`/`asSection` are `ℤ`-linear
(`pull_add`/`pull_zsmul`/`asSection_add`/`asSection_zsmul`). -/
lemma pullAlong_glSmul {S : Scheme.{u}} {E : EllipticCurve S} (N : ℕ) [NeZero N]
    {T : Scheme.{u}} (σ : T ⟶ S) (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
    (L : E.FullLevelPt N) :
    FullLevelPt.pullAlong σ (E.glSmul γ L)
      = (E.baseChange σ).glSmul γ (FullLevelPt.pullAlong σ L) := by
  have key : ∀ (n k : ℤ) (P Q : E.Section),
      Point.asSection E σ (Point.pull E σ (n • P + k • Q))
        = n • Point.asSection E σ (Point.pull E σ P)
          + k • Point.asSection E σ (Point.pull E σ Q) := by
    intro n k P Q
    rw [Point.pull_add, Point.pull_zsmul, Point.pull_zsmul, Point.asSection_add,
      Point.asSection_zsmul, Point.asSection_zsmul]
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact key (((γ : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0).val : ℤ)
      (((γ : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0).val : ℤ) L.1.1 L.1.2
  · exact key (((γ : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 1).val : ℤ)
      (((γ : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 1).val : ℤ) L.1.1 L.1.2

open EllipticCurve in
/-- `EllHom.pullSection` of the first `glSmul`-transformed section is the corresponding
`ℤ`-combination of pulled sections (`glSmul` unfold + `pullSection_add`/`_zsmul`). -/
lemma pullSection_glSmul_fst {R : CommRingCat.{u}} {X Y : EllObj R} (N : ℕ) [NeZero N]
    (f : X ⟶ Y) (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) (M : Y.curve.FullLevelPt N) :
    EllHom.pullSection R f (Y.curve.glSmul γ M).1.1
      = (((γ : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0).val : ℤ) • EllHom.pullSection R f M.1.1
        + (((γ : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0).val : ℤ) • EllHom.pullSection R f M.1.2 := by
  show EllHom.pullSection R f
      ((((γ : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0).val : ℤ) • M.1.1
        + (((γ : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0).val : ℤ) • M.1.2) = _
  rw [EllHom.pullSection_add, EllHom.pullSection_zsmul, EllHom.pullSection_zsmul]

open EllipticCurve in
/-- `EllHom.pullSection` of the second `glSmul`-transformed section. -/
lemma pullSection_glSmul_snd {R : CommRingCat.{u}} {X Y : EllObj R} (N : ℕ) [NeZero N]
    (f : X ⟶ Y) (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) (M : Y.curve.FullLevelPt N) :
    EllHom.pullSection R f (Y.curve.glSmul γ M).1.2
      = (((γ : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 1).val : ℤ) • EllHom.pullSection R f M.1.1
        + (((γ : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 1).val : ℤ) • EllHom.pullSection R f M.1.2 := by
  show EllHom.pullSection R f
      ((((γ : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 1).val : ℤ) • M.1.1
        + (((γ : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 1).val : ℤ) • M.1.2) = _
  rw [EllHom.pullSection_add, EllHom.pullSection_zsmul, EllHom.pullSection_zsmul]

open EllipticCurve in
/-- Section-level restriction identity (first section): pulling the coproduct glue back
to summand `i` recovers `Lf i` pulled to the summand base. -/
lemma coprodFullLevel_restrict_fst {R : CommRingCat.{u}} (N : ℕ) [NeZero N] (X : EllObj R)
    (g : (∐ fun _ : Bool => X.base) ⟶ X.base)
    (hg : ∀ b : Bool, Sigma.ι (fun _ : Bool => X.base) b ≫ g = 𝟙 X.base)
    (Lf : Bool → X.curve.FullLevelPt N) (i : Bool) :
    EllHom.pullSection R (X.pullbackAlongMap g (Sigma.ι (fun _ : Bool => X.base) i))
        (coprodFullLevel N X g hg Lf).1.1
      = (FullLevelPt.pullAlong (Sigma.ι (fun _ : Bool => X.base) i ≫ g) (Lf i)).1.1 := by
  rw [show (coprodFullLevel N X g hg Lf).1.1
        = Point.asSection X.curve g (coprodPoint X g hg (fun b => (Lf b).1.1)) from rfl,
    pullSection_asSection_aux, restrict_coprodPoint]
  rfl

open EllipticCurve in
/-- Section-level restriction identity (second section). -/
lemma coprodFullLevel_restrict_snd {R : CommRingCat.{u}} (N : ℕ) [NeZero N] (X : EllObj R)
    (g : (∐ fun _ : Bool => X.base) ⟶ X.base)
    (hg : ∀ b : Bool, Sigma.ι (fun _ : Bool => X.base) b ≫ g = 𝟙 X.base)
    (Lf : Bool → X.curve.FullLevelPt N) (i : Bool) :
    EllHom.pullSection R (X.pullbackAlongMap g (Sigma.ι (fun _ : Bool => X.base) i))
        (coprodFullLevel N X g hg Lf).1.2
      = (FullLevelPt.pullAlong (Sigma.ι (fun _ : Bool => X.base) i ≫ g) (Lf i)).1.2 := by
  rw [show (coprodFullLevel N X g hg Lf).1.2
        = Point.asSection X.curve g (coprodPoint X g hg (fun b => (Lf b).1.2)) from rfl,
    pullSection_asSection_aux, restrict_coprodPoint]
  rfl

open EllipticCurve in
/-- **[GHC4, the restriction identity]** The naive `Γ_H` problem's restriction of a
coproduct-glued class to a `Bool`-summand `i` is the class of the summand's structure
`Lf i`, pulled to the summand's base (`= pullAlong (Sigma.ι i ≫ g) (Lf i)`). Computes
`gammaHNaiveProblem.map` on a `Quotient.mk` via the section-level identities. -/
lemma coprodFullLevel_restrict {R : CommRingCat.{u}} (N : ℕ) [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N))) (X : EllObj R)
    (g : (∐ fun _ : Bool => X.base) ⟶ X.base)
    (hg : ∀ b : Bool, Sigma.ι (fun _ : Bool => X.base) b ≫ g = 𝟙 X.base)
    (Lf : Bool → X.curve.FullLevelPt N) (i : Bool) :
    (gammaHNaiveProblem R N H).map
        (X.pullbackAlongMap g (Sigma.ι (fun _ : Bool => X.base) i)).op
        (Quotient.mk _ (coprodFullLevel N X g hg Lf))
      = Quotient.mk _
          (FullLevelPt.pullAlong (Sigma.ι (fun _ : Bool => X.base) i ≫ g) (Lf i)) :=
  congrArg (Quotient.mk _)
    (Subtype.ext (Prod.ext (coprodFullLevel_restrict_fst N X g hg Lf i)
      (coprodFullLevel_restrict_snd N X g hg Lf i)))

open EllipticCurve in
set_option backward.isDefEq.respectTransparency false in
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
  intro hrep
  -- A nontrivial element `γ ∈ H`.
  obtain ⟨γ, hγ⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hH
  have hγH : (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) ∈ H := γ.2
  have hγ1 : (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) ≠ 1 := fun h => hγ (Subtype.ext h)
  -- The codiagonal `T = X.base ⨿ X.base → X.base`.
  set g : (∐ fun _ : Bool => X.base) ⟶ X.base := Sigma.desc (fun _ => 𝟙 X.base) with hg_def
  have hg : ∀ b : Bool, Sigma.ι (fun _ : Bool => X.base) b ≫ g = 𝟙 X.base :=
    fun b => by rw [hg_def]; exact Sigma.ι_desc _ _
  -- The diagonal glue `(L, L)` and the twisted glue `(L, γ·L)`.
  set LfA : Bool → X.curve.FullLevelPt N := fun _ => L with hLfA
  set LfB : Bool → X.curve.FullLevelPt N :=
    fun b => bif b then X.curve.glSmul (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) L else L
    with hLfB
  have hLfA_true : LfA true = L := rfl
  have hLfA_false : LfA false = L := rfl
  have hLfB_true : LfB true = X.curve.glSmul (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) L :=
    rfl
  have hLfB_false : LfB false = L := rfl
  obtain ⟨d⟩ := (ModuliProblem.relativelyRepresentable_iff_nonempty_relRepData
    (gammaHNaiveProblem R N H)).mp hrep X
  -- The two global classes restrict equally on both summands, hence are equal (separation).
  have hsep : (Quotient.mk ((X.pullbackAlong g).curve.hOrbitSetoid H)
        (coprodFullLevel N X g hg LfA))
      = Quotient.mk _ (coprodFullLevel N X g hg LfB) := by
    refine relRepData_sep_coprod R d g _ _ (fun i => ?_)
    refine (coprodFullLevel_restrict N H X g hg LfA i).trans
      (Eq.trans ?_ (coprodFullLevel_restrict N H X g hg LfB i).symm)
    cases i with
    | false => rw [hLfA_false, hLfB_false]
    | true =>
      rw [hLfA_true, hLfB_true]
      exact Quotient.sound ⟨(γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)), hγH,
        (pullAlong_glSmul N (Sigma.ι (fun _ : Bool => X.base) true ≫ g)
          (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) L).symm⟩
  -- Unpack the orbit relation on the coproduct base.
  obtain ⟨h, hhH, hhAB⟩ := Quotient.exact hsep
  -- Restricting `glSmul h A = B` to the `false` summand (where `A`, `B` agree) forces `h = 1`.
  have hh1 : h = 1 := by
    refine glSmul_eq_one_of_eq_self N hinv
      (X.pullbackAlong (Sigma.ι (fun _ : Bool => X.base) false ≫ g))
      hne h (FullLevelPt.pullAlong (Sigma.ι (fun _ : Bool => X.base) false ≫ g) L)
      (Subtype.ext (Prod.ext ?_ ?_))
    · have hf1 := congrArg (fun M => EllHom.pullSection R
        (X.pullbackAlongMap g (Sigma.ι (fun _ : Bool => X.base) false)) M.1.1) hhAB
      rw [pullSection_glSmul_fst, coprodFullLevel_restrict_fst, coprodFullLevel_restrict_snd,
        coprodFullLevel_restrict_fst, hLfA_false, hLfB_false] at hf1
      exact hf1
    · have hf2 := congrArg (fun M => EllHom.pullSection R
        (X.pullbackAlongMap g (Sigma.ι (fun _ : Bool => X.base) false)) M.1.2) hhAB
      rw [pullSection_glSmul_snd, coprodFullLevel_restrict_fst, coprodFullLevel_restrict_snd,
        coprodFullLevel_restrict_snd, hLfA_false, hLfB_false] at hf2
      exact hf2
  -- With `h = 1`, `A = B`; restricting to `true` forces `γ = 1`, a contradiction.
  rw [hh1, EllipticCurve.glSmul_one] at hhAB
  have ht1 := congrArg (fun M => EllHom.pullSection R
    (X.pullbackAlongMap g (Sigma.ι (fun _ : Bool => X.base) true)) M.1.1) hhAB
  have ht2 := congrArg (fun M => EllHom.pullSection R
    (X.pullbackAlongMap g (Sigma.ι (fun _ : Bool => X.base) true)) M.1.2) hhAB
  rw [coprodFullLevel_restrict_fst, coprodFullLevel_restrict_fst, hLfA_true, hLfB_true] at ht1
  rw [coprodFullLevel_restrict_snd, coprodFullLevel_restrict_snd, hLfA_true, hLfB_true] at ht2
  have hpull : FullLevelPt.pullAlong (Sigma.ι (fun _ : Bool => X.base) true ≫ g) L
      = FullLevelPt.pullAlong (Sigma.ι (fun _ : Bool => X.base) true ≫ g)
          (X.curve.glSmul (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) L) :=
    Subtype.ext (Prod.ext ht1 ht2)
  rw [pullAlong_glSmul] at hpull
  exact hγ1 (glSmul_eq_one_of_eq_self N hinv
    (X.pullbackAlong (Sigma.ι (fun _ : Bool => X.base) true ≫ g)) hne
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
    (FullLevelPt.pullAlong (Sigma.ι (fun _ : Bool => X.base) true ≫ g) L) hpull.symm)

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
