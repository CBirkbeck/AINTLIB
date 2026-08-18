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
import ModularCurves.Moduli.LevelSpaceEtaleClose
import ModularCurves.ModularCurve.YFullRoute
import ModularCurves.GroupScheme.DeligneOrder
import ModularCurves.ForMathlib.RelativeInvariantSpec
import ModularCurves.ForMathlib.SchemeActionFree
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

-- v4.33 bump: component types coming from semireducible `baseChange*`/`pullback` defs are
-- defeq only after delta, which `rw`/`simp`/`calc` will not do at `implicit` transparency.
set_option backward.isDefEq.respectTransparency.types false

universe u

-- The `MulByHomFibresGlobal` import subtree (BB-QF closure via `Torsion`) enlarges the
-- instance pool; `map_zsmul`/`map_zero` synthesis on `≃+` needs more headroom here.
set_option synthInstance.maxHeartbeats 80000

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
  intro T t γ hγ hfix
  rw [isEmpty_iff]
  intro x
  -- The base composite and the value it classifies over `E ×_S T`.
  set g : T ⟶ X.base := t ≫ e.f with hg
  set a := e.eqv g ⟨t, hg.symm⟩ with ha
  -- `equivariant` + the fixed-point hypothesis: `a` is fixed by `φ γ⁻¹`.
  have heq := e.equivariant g ⟨t, hg.symm⟩ γ
  have hcongr : e.eqv g ⟨t ≫ e.σZ.hom γ, by rw [Category.assoc, e.over_base, hg.symm]⟩ = a :=
    congrArg (e.eqv g) (Subtype.ext hfix)
  rw [hcongr] at heq
  -- Freeness over the nonempty base `T` kills the fixed point.
  exact hfree (X.pullbackAlong g) ⟨x⟩ γ⁻¹ (inv_ne_one.mpr hγ) a heq.symm

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

/- `SchemeAction.basePullback` (the base change of a scheme action lying over `S`
along `g : T ⟶ S`) now lives in `ForMathlib/RelativeInvariantSpec.lean` — the local
copy that used to sit here was hoisted verbatim (T-RIS8 dedup). -/

open EllObj in
/-- **The base change of an equivariant relative representation datum** along an
`Ell/R`-morphism ([GHB7-2a], equivariant upgrade): the underlying datum is
`RelRepData.pullback`, the action is `SchemeAction.basePullback`, and the geometric
clauses transport by base-change stability. Feeds the per-object choices of the [GHB7]
assembly with functorial comparisons. -/
noncomputable def ModuliProblem.EquivariantRelRepData.pullback {R : CommRingCat.{u}}
    {Q : ModuliProblem R}
    {G : Type*} [Group G] [Finite G] {φ : G →* Aut Q} {X' X : EllObj R}
    (d : ModuliProblem.EquivariantRelRepData φ X) (ψ : X' ⟶ X) :
    ModuliProblem.EquivariantRelRepData φ X' where
  toRelRepData := d.toRelRepData.pullback ψ
  σZ := d.σZ.basePullback d.f d.over_base ψ.baseHom
  over_base γ := by
    show (d.σZ.basePullback d.f d.over_base ψ.baseHom).hom γ ≫
      pullback.snd d.f ψ.baseHom = pullback.snd d.f ψ.baseHom
    simp only [SchemeAction.basePullback, pullback.lift_snd, Category.comp_id]
  equivariant := by
    intro T g h γ
    have hbfst : (d.σZ.basePullback d.f d.over_base ψ.baseHom).hom γ ≫
        pullback.fst d.f ψ.baseHom = pullback.fst d.f ψ.baseHom ≫ d.σZ.hom γ := by
      simp only [SchemeAction.basePullback, pullback.lift_fst]
    have hbsnd : (d.σZ.basePullback d.f d.over_base ψ.baseHom).hom γ ≫
        pullback.snd d.f ψ.baseHom = pullback.snd d.f ψ.baseHom := by
      simp only [SchemeAction.basePullback, pullback.lift_snd, Category.comp_id]
    -- re-anchor the three-layer classifying bijection (`rfl`-graded)
    have hval : ∀ (h' : { h : T ⟶ (d.toRelRepData.pullback ψ).Z //
          h ≫ (d.toRelRepData.pullback ψ).f = g })
        (p : (h'.1 ≫ pullback.fst d.f ψ.baseHom) ≫ d.f = g ≫ ψ.baseHom),
        (d.toRelRepData.pullback ψ).eqv g h' =
          Q.map (EllObj.toPullbackAlong (X'.pullbackAlongπ g ≫ ψ)).op
            (d.eqv (g ≫ ψ.baseHom) ⟨h'.1 ≫ pullback.fst d.f ψ.baseHom, p⟩) :=
      fun h' p => rfl
    -- the whole identity over a fresh reduced-typed section, instantiated at `h` last
    have key : ∀ (v : T ⟶ CategoryTheory.Limits.pullback d.f ψ.baseHom)
        (hv2 : v ≫ pullback.snd d.f ψ.baseHom = g),
        (d.toRelRepData.pullback ψ).eqv g
          ⟨v ≫ (d.σZ.basePullback d.f d.over_base ψ.baseHom).hom γ,
            show (v ≫ (d.σZ.basePullback d.f d.over_base ψ.baseHom).hom γ) ≫
                pullback.snd d.f ψ.baseHom = g by
              rw [Category.assoc, hbsnd, hv2]⟩ =
        (φ γ⁻¹).hom.app (Opposite.op (X'.pullbackAlong g))
          ((d.toRelRepData.pullback ψ).eqv g ⟨v, hv2⟩) := by
      intro v hv2
      have hmred : (v ≫ (d.σZ.basePullback d.f d.over_base ψ.baseHom).hom γ) ≫
          pullback.snd d.f ψ.baseHom = g := by
        rw [Category.assoc, hbsnd, hv2]
      have hp1 : ((v ≫ (d.σZ.basePullback d.f d.over_base ψ.baseHom).hom γ) ≫
          pullback.fst d.f ψ.baseHom) ≫ d.f = g ≫ ψ.baseHom := by
        calc ((v ≫ (d.σZ.basePullback d.f d.over_base ψ.baseHom).hom γ) ≫
                pullback.fst d.f ψ.baseHom) ≫ d.f
            = (v ≫ (d.σZ.basePullback d.f d.over_base ψ.baseHom).hom γ) ≫
                pullback.fst d.f ψ.baseHom ≫ d.f := Category.assoc _ _ _
          _ = (v ≫ (d.σZ.basePullback d.f d.over_base ψ.baseHom).hom γ) ≫
                pullback.snd d.f ψ.baseHom ≫ ψ.baseHom := by
              rw [pullback.condition]
          _ = ((v ≫ (d.σZ.basePullback d.f d.over_base ψ.baseHom).hom γ) ≫
                pullback.snd d.f ψ.baseHom) ≫ ψ.baseHom := (Category.assoc _ _ _).symm
          _ = g ≫ ψ.baseHom := congrArg (· ≫ ψ.baseHom) hmred
      have hp2 : (v ≫ pullback.fst d.f ψ.baseHom) ≫ d.f = g ≫ ψ.baseHom := by
        calc (v ≫ pullback.fst d.f ψ.baseHom) ≫ d.f
            = v ≫ pullback.fst d.f ψ.baseHom ≫ d.f := Category.assoc _ _ _
          _ = v ≫ pullback.snd d.f ψ.baseHom ≫ ψ.baseHom := by rw [pullback.condition]
          _ = (v ≫ pullback.snd d.f ψ.baseHom) ≫ ψ.baseHom := (Category.assoc _ _ _).symm
          _ = g ≫ ψ.baseHom := congrArg (· ≫ ψ.baseHom) hv2
      rw [hval ⟨v ≫ (d.σZ.basePullback d.f d.over_base ψ.baseHom).hom γ, hmred⟩ hp1,
        hval ⟨v, hv2⟩ hp2]
      rw [show (⟨(⟨v ≫ (d.σZ.basePullback d.f d.over_base ψ.baseHom).hom γ, hmred⟩ :
            { hh : T ⟶ (d.toRelRepData.pullback ψ).Z //
              hh ≫ (d.toRelRepData.pullback ψ).f = g }).1 ≫
            pullback.fst d.f ψ.baseHom, hp1⟩ :
          { kk : T ⟶ d.Z // kk ≫ d.f = g ≫ ψ.baseHom }) =
        ⟨(v ≫ pullback.fst d.f ψ.baseHom) ≫ d.σZ.hom γ, by
          rw [Category.assoc, d.over_base γ]; exact hp2⟩ from
        Subtype.ext (by
          show (v ≫ (d.σZ.basePullback d.f d.over_base ψ.baseHom).hom γ) ≫
              pullback.fst d.f ψ.baseHom =
            (v ≫ pullback.fst d.f ψ.baseHom) ≫ d.σZ.hom γ
          rw [Category.assoc, hbfst, ← Category.assoc])]
      rw [d.equivariant (g ≫ ψ.baseHom) ⟨v ≫ pullback.fst d.f ψ.baseHom, hp2⟩ γ]
      exact (NatTrans.naturality_apply (φ γ⁻¹).hom
        (EllObj.toPullbackAlong (X'.pullbackAlongπ g ≫ ψ)).op _).symm
    exact key h.1 h.2
  finite := by
    haveI := d.finite
    exact MorphismProperty.pullback_snd _ _ d.finite
  etale := by
    haveI := d.etale
    show Etale (pullback.snd d.f ψ.baseHom)
    infer_instance

/-- **The comparison morphism of equivariant data is equivariant** ([GHB7-2b],
equivariant upgrade): for two equivariant relative representation data of the same
problem at the same object, the canonical comparison `RelRepData.compare` intertwines
the two actions. Lets the [GHB7] per-object quotients glue functorially. -/
theorem ModuliProblem.EquivariantRelRepData.compare_equivariant {R : CommRingCat.{u}}
    {Q : ModuliProblem R} {G : Type*} [Group G] [Finite G] {φ : G →* Aut Q}
    {X : EllObj R} (d₁ d₂ : ModuliProblem.EquivariantRelRepData φ X) (γ : G) :
    d₁.σZ.hom γ ≫ (d₁.toRelRepData.compare d₂.toRelRepData).1 =
      (d₁.toRelRepData.compare d₂.toRelRepData).1 ≫ d₂.σZ.hom γ := by
  have m₁ : (d₁.σZ.hom γ ≫ (d₁.toRelRepData.compare d₂.toRelRepData).1) ≫ d₂.f =
      d₁.f := by
    rw [Category.assoc, (d₁.toRelRepData.compare d₂.toRelRepData).2, d₁.over_base γ]
  have m₂ : ((d₁.toRelRepData.compare d₂.toRelRepData).1 ≫ d₂.σZ.hom γ) ≫ d₂.f =
      d₁.f := by
    rw [Category.assoc, d₂.over_base γ, (d₁.toRelRepData.compare d₂.toRelRepData).2]
  have e1 : d₂.eqv d₁.f ⟨d₁.σZ.hom γ ≫ (d₁.toRelRepData.compare d₂.toRelRepData).1,
        m₁⟩ = d₁.eqv d₁.f ⟨d₁.σZ.hom γ, d₁.over_base γ⟩ :=
    ModuliProblem.RelRepData.eqv_comp_compare d₁.toRelRepData d₂.toRelRepData d₁.f
      ⟨d₁.σZ.hom γ, d₁.over_base γ⟩
  have e2 : d₁.eqv d₁.f ⟨d₁.σZ.hom γ, d₁.over_base γ⟩ =
      (φ γ⁻¹).hom.app (Opposite.op (X.pullbackAlong d₁.f))
        (d₁.eqv d₁.f ⟨𝟙 d₁.Z, Category.id_comp d₁.f⟩) := by
    rw [show (⟨d₁.σZ.hom γ, d₁.over_base γ⟩ :
        { s : d₁.Z ⟶ d₁.Z // s ≫ d₁.f = d₁.f }) =
      ⟨𝟙 d₁.Z ≫ d₁.σZ.hom γ, by rw [Category.id_comp]; exact d₁.over_base γ⟩ from
      Subtype.ext (Category.id_comp _).symm]
    exact d₁.equivariant d₁.f ⟨𝟙 d₁.Z, Category.id_comp d₁.f⟩ γ
  have e3 : d₂.eqv d₁.f ⟨(d₁.toRelRepData.compare d₂.toRelRepData).1 ≫ d₂.σZ.hom γ,
        m₂⟩ =
      (φ γ⁻¹).hom.app (Opposite.op (X.pullbackAlong d₁.f))
        (d₂.eqv d₁.f (d₁.toRelRepData.compare d₂.toRelRepData)) :=
    d₂.equivariant d₁.f (d₁.toRelRepData.compare d₂.toRelRepData) γ
  have e4 : d₂.eqv d₁.f (d₁.toRelRepData.compare d₂.toRelRepData) =
      d₁.eqv d₁.f ⟨𝟙 d₁.Z, Category.id_comp d₁.f⟩ :=
    ModuliProblem.RelRepData.eqv_compare d₁.toRelRepData d₂.toRelRepData
  have key : (⟨d₁.σZ.hom γ ≫ (d₁.toRelRepData.compare d₂.toRelRepData).1, m₁⟩ :
      { s : d₁.Z ⟶ d₂.Z // s ≫ d₂.f = d₁.f }) =
      ⟨(d₁.toRelRepData.compare d₂.toRelRepData).1 ≫ d₂.σZ.hom γ, m₂⟩ :=
    (d₂.eqv d₁.f).injective (by rw [e1, e2, e3, e4])
  exact congrArg Subtype.val key

/-- **[GHB3] (KM 7.1.3(3) existence half; Loeffler Prop 3.6.1's affine patching)** —
"For any E/S/R, the quotient scheme 𝒫_{E/S}/G exists"; Loeffler 3.6.1 (verbatim): "for
X = Spec(A) affine, Spec(A^G) works, and one can show that these patch nicely. (One
needs quasiprojectiveness and finiteness of G here.)" — our patching datum is the
`IsAffineHom`-preimage atlas of affine opens of `S` (stable by `hover`, affine by
`IsAffineHom`), fed to `SchemeAction.quotient`/`quotientπ`/`hom_quotientπ`/
`quotientπ_hom_ext`/`existsUnique_quotientπ_lift` (T-Q5, all PROVEN). DIAGONAL-FREE
(T-RIS8): the body now delegates to the relative-invariant-Spec engine
(`exists_quotient_of_isAffineHom_rel`, `ForMathlib/RelativeInvariantSpec.lean`), which
needs no hypothesis on the diagonal of `Z` — the quotient is glued from
`Spec Γ(Z, f⁻¹U)ᴳ` over the directed affine cover of `S`. -/
theorem _root_.AlgebraicGeometry.SchemeAction.exists_quotient_of_isAffineHom
    {G : Type*} [Group G] [Finite G]
    {Z S : Scheme.{u}}
    (σ : SchemeAction G Z) (f : Z ⟶ S) [IsAffineHom f]
    (hover : ∀ γ : G, σ.hom γ ≫ f = f) :
    ∃ (Z₀ : Scheme.{u}) (π : Z ⟶ Z₀) (f₀ : Z₀ ⟶ S), π ≫ f₀ = f ∧
      (∀ γ : G, σ.hom γ ≫ π = π) ∧
      ∀ {Y : Scheme.{u}} (F : Z ⟶ Y), (∀ γ : G, σ.hom γ ≫ F = F) →
        ∃! q : Z₀ ⟶ Y, π ≫ q = F :=
  σ.exists_quotient_of_isAffineHom_rel f hover

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
    {Z S Z₀ : Scheme.{u}}
    (σ : SchemeAction G Z) (f : Z ⟶ S) [IsAffineHom f]
    (hover : ∀ γ : G, σ.hom γ ≫ f = f)
    (hfree : ∀ {T : Scheme.{u}} (t : T ⟶ Z) (γ : G), γ ≠ 1 →
      t ≫ σ.hom γ = t → IsEmpty T)
    (π : Z ⟶ Z₀) (f₀ : Z₀ ⟶ S) (hπf : π ≫ f₀ = f)
    (hπinv : ∀ γ : G, σ.hom γ ≫ π = π)
    (hdesc : ∀ {Y : Scheme.{u}} (F : Z ⟶ Y), (∀ γ : G, σ.hom γ ≫ F = F) →
      ∃! q : Z₀ ⟶ Y, π ≫ q = F) :
    IsFinite π ∧ Etale π ∧ Surjective π := by
  classical
  -- The concrete diagonal-free quotient (`ForMathlib/RelativeInvariantSpec.lean`).
  set π₀ := σ.relQuotientπ f hover with hπ₀def
  haveI hFin₀ : IsFinite π₀ := σ.isFinite_relQuotientπ_of_free f hover hfree
  haveI hEt₀ : Etale π₀ := σ.etale_relQuotientπ_of_free f hover hfree
  haveI hSurj₀ : Surjective π₀ := σ.surjective_relQuotientπ_of_free f hover
  have hπ₀inv : ∀ g : G, σ.hom g ≫ π₀ = π₀ := σ.hom_comp_relQuotientπ f hover
  -- Unique iso between the abstract quotient `Z₀` and the concrete one.
  obtain ⟨q, hq, -⟩ := hdesc π₀ hπ₀inv
  obtain ⟨q', hq', -⟩ := σ.existsUnique_relQuotientπ_lift f hover π hπinv
  have hqq' : q ≫ q' = 𝟙 Z₀ := by
    obtain ⟨_, -, huniq⟩ := hdesc π hπinv
    rw [huniq (q ≫ q') (show π ≫ (q ≫ q') = π by rw [← Category.assoc, hq, hq']),
      huniq (𝟙 Z₀) (show π ≫ 𝟙 Z₀ = π by rw [Category.comp_id])]
  have hq'q : q' ≫ q = 𝟙 _ := by
    obtain ⟨_, -, huniq⟩ := σ.existsUnique_relQuotientπ_lift f hover π₀ hπ₀inv
    rw [huniq (q' ≫ q) (show π₀ ≫ (q' ≫ q) = π₀ by rw [← Category.assoc, hq', hq]),
      huniq (𝟙 _) (show π₀ ≫ 𝟙 _ = π₀ by rw [Category.comp_id])]
  haveI : IsIso q := ⟨q', hqq', hq'q⟩
  refine ⟨(MorphismProperty.cancel_right_of_respectsIso (P := @IsFinite) π q).mp ?_,
    (MorphismProperty.cancel_right_of_respectsIso (P := @Etale) π q).mp ?_,
    (MorphismProperty.cancel_right_of_respectsIso (P := @Surjective) π q).mp ?_⟩
  · rw [hq]; exact hFin₀
  · rw [hq]; exact hEt₀
  · rw [hq]; exact hSurj₀

/-- **[GHB5] (KM 7.1.3(3c) — gate [A711-BC]; the crux of (Q2))** — verbatim: "there is
a natural S-morphism (𝒫_{E/S})/G → (𝒫/G)_{E/S}, which is bijective on geometric
points. It is an isomorphism if any of the following conditions hold: … c) G operates
freely on 𝒫." Formulated as: the base change `pullback f₀ g` of a quotient satisfies
the quotient universal property for the base-changed action — so "quotient commutes
with base change" for free actions. Chart-local algebra core:
`fixedPointsBaseChange_bijective_of_isFreeAlgebraAction`
(`ForMathlib/InvariantTorsor.lean`, KM A7.1.2 "∗(A, G, R, R′) for every R′" — PROVEN,
[A711-BC]); without freeness the statement is FALSE (KM lists (c) as a sufficient
condition; non-free quotients do not commute with base change). -/
theorem _root_.AlgebraicGeometry.SchemeAction.exists_quotient_baseChange_of_free
    {G : Type*} [Group G]
    [Finite G] {Z S Z₀ : Scheme.{u}}
    (σ : SchemeAction G Z) (f : Z ⟶ S)
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
  set πT : pullback f g ⟶ pullback f₀ g :=
    pullback.map f g f₀ g π (𝟙 T) (𝟙 S) (by rw [Category.comp_id]; exact hπf.symm)
      (by rw [Category.comp_id, Category.id_comp]) with hπTdef
  have hsnd : πT ≫ pullback.snd f₀ g = pullback.snd f g := by
    rw [hπTdef, pullback.lift_snd, Category.comp_id]
  have hfst : πT ≫ pullback.fst f₀ g = pullback.fst f g ≫ π := by
    rw [hπTdef, pullback.lift_fst]
  have hbfst : ∀ γ : G, (σ.basePullback f hover g).hom γ ≫ pullback.fst f g
      = pullback.fst f g ≫ σ.hom γ := fun γ => by
    simp only [SchemeAction.basePullback, pullback.lift_fst]
  have hbsnd : ∀ γ : G, (σ.basePullback f hover g).hom γ ≫ pullback.snd f g
      = pullback.snd f g := fun γ => by
    simp only [SchemeAction.basePullback, pullback.lift_snd, Category.comp_id]
  refine ⟨πT, hsnd, hfst, ?_, ?_⟩
  · -- invariance under the base-changed action
    intro γ
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hfst, ← Category.assoc, hbfst, Category.assoc, hπinv]
    · rw [Category.assoc, hsnd, hbsnd]
  · -- the base-change universal property (KM 7.1.3(3c) crux): identify the abstract
    -- quotient with the concrete one (`hdesc`-uniqueness iso `q`), identify
    -- `pullback f g` with the base change of the concrete `quotientπ` along
    -- `jc := pullback.fst f₀ g ≫ q` (the comparison iso `E`, with `E ≫ πT` = the
    -- base-changed projection), and descend through [GHB5a]
    -- `exists_quotientπ_lift_baseChange`; uniqueness because the base-changed
    -- projection is an epimorphism (`epi_pullback_snd_quotientπ`, free actions).
    intro Y F hF
    classical
    -- the concrete diagonal-free quotient (`ForMathlib/RelativeInvariantSpec.lean`)
    have hπinv₀ : ∀ γ : G, σ.hom γ ≫ σ.relQuotientπ f hover = σ.relQuotientπ f hover :=
      σ.hom_comp_relQuotientπ f hover
    -- the unique iso between the abstract and the concrete quotient
    obtain ⟨q, hq, -⟩ := hdesc (σ.relQuotientπ f hover) hπinv₀
    obtain ⟨q', hq', -⟩ := σ.existsUnique_relQuotientπ_lift f hover π hπinv
    have hqq' : q ≫ q' = 𝟙 Z₀ := by
      obtain ⟨_, -, huniq⟩ := hdesc π hπinv
      rw [huniq (q ≫ q') (show π ≫ (q ≫ q') = π by rw [← Category.assoc, hq, hq']),
        huniq (𝟙 Z₀) (show π ≫ 𝟙 Z₀ = π by rw [Category.comp_id])]
    have hq'q : q' ≫ q = 𝟙 _ := by
      obtain ⟨_, -, huniq⟩ := σ.existsUnique_relQuotientπ_lift f hover (σ.relQuotientπ f hover) hπinv₀
      rw [huniq (q' ≫ q) (show (σ.relQuotientπ f hover) ≫ (q' ≫ q) = (σ.relQuotientπ f hover) by rw [← Category.assoc, hq', hq]),
        huniq (𝟙 _) (show (σ.relQuotientπ f hover) ≫ 𝟙 _ = (σ.relQuotientπ f hover) by rw [Category.comp_id])]
    haveI : IsIso q := ⟨q', hqq', hq'q⟩
    -- the base map into the concrete quotient, and the comparison iso of base changes
    set jc : pullback f₀ g ⟶ σ.relQuotient f hover := pullback.fst f₀ g ≫ q with hjc
    have hkey : pullback.fst (σ.relQuotientπ f hover) jc ≫ π = pullback.snd (σ.relQuotientπ f hover) jc ≫ pullback.fst f₀ g := by
      have h1 : (pullback.fst (σ.relQuotientπ f hover) jc ≫ π) ≫ q =
          (pullback.snd (σ.relQuotientπ f hover) jc ≫ pullback.fst f₀ g) ≫ q := by
        rw [Category.assoc, hq, pullback.condition (f := (σ.relQuotientπ f hover)) (g := jc), hjc,
          Category.assoc]
      exact (cancel_mono q).mp h1
    have hsq : pullback.fst (σ.relQuotientπ f hover) jc ≫ f = (pullback.snd (σ.relQuotientπ f hover) jc ≫ pullback.snd f₀ g) ≫ g :=
      calc pullback.fst (σ.relQuotientπ f hover) jc ≫ f
          = pullback.fst (σ.relQuotientπ f hover) jc ≫ π ≫ f₀ :=
            congrArg (pullback.fst (σ.relQuotientπ f hover) jc ≫ ·) hπf.symm
        _ = (pullback.fst (σ.relQuotientπ f hover) jc ≫ π) ≫ f₀ :=
            (Category.assoc _ _ _).symm
        _ = (pullback.snd (σ.relQuotientπ f hover) jc ≫ pullback.fst f₀ g) ≫ f₀ :=
            congrArg (· ≫ f₀) hkey
        _ = pullback.snd (σ.relQuotientπ f hover) jc ≫ pullback.fst f₀ g ≫ f₀ :=
            Category.assoc _ _ _
        _ = pullback.snd (σ.relQuotientπ f hover) jc ≫ pullback.snd f₀ g ≫ g :=
            congrArg (pullback.snd (σ.relQuotientπ f hover) jc ≫ ·)
              (pullback.condition (f := f₀) (g := g))
        _ = (pullback.snd (σ.relQuotientπ f hover) jc ≫ pullback.snd f₀ g) ≫ g :=
            (Category.assoc _ _ _).symm
    set E : pullback (σ.relQuotientπ f hover) jc ⟶ pullback f g :=
      pullback.lift (pullback.fst (σ.relQuotientπ f hover) jc) (pullback.snd (σ.relQuotientπ f hover) jc ≫ pullback.snd f₀ g) hsq
      with hE
    have hEfst : E ≫ pullback.fst f g = pullback.fst (σ.relQuotientπ f hover) jc := by
      rw [hE]; exact pullback.lift_fst _ _ _
    have hEsnd : E ≫ pullback.snd f g = pullback.snd (σ.relQuotientπ f hover) jc ≫ pullback.snd f₀ g := by
      rw [hE]; exact pullback.lift_snd _ _ _
    -- `E ≫ πT` is the concrete base-changed projection
    have hEπT : E ≫ πT = pullback.snd (σ.relQuotientπ f hover) jc := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, hfst, ← Category.assoc, hEfst, hkey]
      · rw [Category.assoc, hsnd, hEsnd]
    -- `E` is an isomorphism, with inverse assembled from `πT`
    have hsq' : pullback.fst f g ≫ (σ.relQuotientπ f hover) = πT ≫ jc := by
      rw [← hq, hjc, ← Category.assoc, ← hfst, Category.assoc]
    set E' : pullback f g ⟶ pullback (σ.relQuotientπ f hover) jc :=
      pullback.lift (pullback.fst f g) πT hsq' with hE'
    have hE'fst : E' ≫ pullback.fst (σ.relQuotientπ f hover) jc = pullback.fst f g := by
      rw [hE']; exact pullback.lift_fst _ _ _
    have hE'snd : E' ≫ pullback.snd (σ.relQuotientπ f hover) jc = πT := by
      rw [hE']; exact pullback.lift_snd _ _ _
    haveI : IsIso E := by
      refine ⟨E', ?_, ?_⟩
      · refine pullback.hom_ext ?_ ?_
        · rw [Category.assoc, hE'fst, Category.id_comp, hEfst]
        · rw [Category.assoc, hE'snd, Category.id_comp, hEπT]
      · refine pullback.hom_ext ?_ ?_
        · rw [Category.assoc, hEfst, Category.id_comp, hE'fst]
        · rw [Category.assoc, hEsnd, Category.id_comp, ← Category.assoc, hE'snd, hsnd]
    -- the comparison intertwines the actions
    have hEact : ∀ γ : G, E ≫ (σ.basePullback f hover g).hom γ =
        σ.pullbackRelQSMul f hover jc γ ≫ E := by
      intro γ
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, hbfst, ← Category.assoc, hEfst, Category.assoc, hEfst,
          SchemeAction.pullbackRelQSMul_fst]
      · rw [Category.assoc, hbsnd, hEsnd, Category.assoc, hEsnd, ← Category.assoc,
          SchemeAction.pullbackRelQSMul_snd]
    -- existence of the descent, through the concrete engine [GHB5a]
    have hFE : ∀ γ : G, σ.pullbackRelQSMul f hover jc γ ≫ (E ≫ F) = E ≫ F := by
      intro γ
      rw [← Category.assoc, ← hEact γ, Category.assoc, hF γ]
    obtain ⟨q₀, hq₀⟩ := σ.exists_relQuotientπ_lift_baseChange f hover hfree jc
      (E ≫ F) hFE
    haveI : Epi (pullback.snd (σ.relQuotientπ f hover) jc) :=
      σ.epi_pullback_snd_relQuotientπ f hover hfree jc
    refine ⟨q₀, ?_, ?_⟩
    · show πT ≫ q₀ = F
      rw [← cancel_epi E, ← Category.assoc, hEπT]
      exact hq₀
    · intro q₁ hq₁
      have hq₁' : πT ≫ q₁ = F := hq₁
      rw [← cancel_epi (pullback.snd (σ.relQuotientπ f hover) jc), hq₀, ← hEπT,
        Category.assoc, hq₁']

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
`B`-submodule of the finite `B`-module `A`; it does NOT need this abstract lemma.

**[2026-07-13, GH] The PRIMARY route has LANDED** (`SchemeAction.quotient_desc_finite_etale`,
`ForMathlib/SchemeActionFree.lean`, axiom-clean via `ForMathlib/EtaleCancellation.lean`) and
`QuotPkg.f₀_finite_etale` now routes through it — **nothing in the pipeline consumes this
abstract statement any more**. It stays as the [GH-DESC-GAP] marker for the general fppf
source-descent (its finite-half needs Chevalley's "affine descends along finite surjective",
absent from mathlib); close it or upstream it when that lands. -/
theorem _root_.AlgebraicGeometry.isFinite_etale_of_comp_of_finite_etale_surjective
    {Z Z₀ S : Scheme.{u}}
    (π : Z ⟶ Z₀) (f₀ : Z₀ ⟶ S) [IsFinite π] [Etale π] [Surjective π]
    (hfin : IsFinite (π ≫ f₀)) (het : Etale (π ≫ f₀)) :
    IsFinite f₀ ∧ Etale f₀ := by
  sorry

end SchemeQuotientLayer

namespace ModuliProblem

variable {R : CommRingCat.{u}}

/-- The chosen-quotient package at one object ([GHB7] assembly unit): an equivariant
relative representation datum together with a quotient of its total space by the
action, i.e. [GHB3]'s output bundled with its input. All fields are DATA chosen once
per object by the assembly; every comparison between two packages (or a package and a
base change) is rigid by the descent-uniqueness field `hdesc`. -/
structure QuotPkg {Q : ModuliProblem R} {G : Type*} [Group G] [Finite G]
    (φ : G →* Aut Q) (X : EllObj R) where
  /-- The equivariant relative representation datum. -/
  d : EquivariantRelRepData φ X
  /-- The quotient scheme `Z/G`. -/
  Z₀ : Scheme.{u}
  /-- The quotient projection. -/
  π : d.Z ⟶ Z₀
  /-- The descended structure map. -/
  f₀ : Z₀ ⟶ X.base
  hπf : π ≫ f₀ = d.f
  hπinv : ∀ γ : G, d.σZ.hom γ ≫ π = π
  hdesc : ∀ {Y : Scheme.{u}} (F : d.Z ⟶ Y), (∀ γ : G, d.σZ.hom γ ≫ F = F) →
    ∃! q : Z₀ ⟶ Y, π ≫ q = F

/-- Every object carries a quotient package ([GHB3] + choice of datum). -/
theorem nonempty_quotPkg {Q : ModuliProblem R} {G : Type*} [Group G] [Finite G]
    (φ : G →* Aut Q) (hdata : ∀ X : EllObj R, Nonempty (EquivariantRelRepData φ X))
    (X : EllObj R) :
    Nonempty (QuotPkg φ X) := by
  obtain ⟨d⟩ := hdata X
  haveI := d.finite
  haveI : IsAffineHom d.f := inferInstance
  obtain ⟨Z₀, π, f₀, hπf, hπinv, hdesc⟩ :=
    AlgebraicGeometry.SchemeAction.exists_quotient_of_isAffineHom d.σZ d.f d.over_base
  exact ⟨⟨d, Z₀, π, f₀, hπf, hπinv, hdesc⟩⟩

/-- The projection of a quotient package is finite étale surjective ([GHB4] applied to
the package; needs freeness). -/
theorem QuotPkg.π_finite_etale_surjective {Q : ModuliProblem R} {G : Type*} [Group G]
    [Finite G] {φ : G →* Aut Q} {X : EllObj R} (p : QuotPkg φ X)
    (hfree : FreeAction φ) :
    IsFinite p.π ∧ Etale p.π ∧ Surjective p.π := by
  haveI := p.d.finite
  haveI : IsAffineHom p.d.f := inferInstance
  exact AlgebraicGeometry.SchemeAction.quotientπ_finite_etale_surjective p.d.σZ p.d.f
    p.d.over_base (p.d.free_on_points hfree) p.π p.f₀ p.hπf p.hπinv p.hdesc

/-- The descended structure map of a quotient package is finite étale (KM 7.1.3(6)
sharpened; **[GHB6] discharged** by the chart-local split-cover route
`SchemeAction.quotient_desc_finite_etale` — trace-retract étale cancellation over each
affine chart of the base, `ForMathlib/EtaleCancellation.lean` +
`ForMathlib/SchemeActionFree.lean`). -/
theorem QuotPkg.f₀_finite_etale {Q : ModuliProblem R} {G : Type*} [Group G]
    [Finite G] {φ : G →* Aut Q} {X : EllObj R} (p : QuotPkg φ X)
    (hfree : FreeAction φ) :
    IsFinite p.f₀ ∧ Etale p.f₀ := by
  haveI := p.d.finite
  haveI : IsAffineHom p.d.f := inferInstance
  classical
  -- the `hdesc`-iso to the concrete diagonal-free quotient
  have hπinv₀ : ∀ γ : G, p.d.σZ.hom γ ≫ p.d.σZ.relQuotientπ p.d.f p.d.over_base =
      p.d.σZ.relQuotientπ p.d.f p.d.over_base :=
    p.d.σZ.hom_comp_relQuotientπ p.d.f p.d.over_base
  obtain ⟨q, hq, -⟩ := p.hdesc (p.d.σZ.relQuotientπ p.d.f p.d.over_base) hπinv₀
  obtain ⟨q', hq', -⟩ :=
    p.d.σZ.existsUnique_relQuotientπ_lift p.d.f p.d.over_base p.π p.hπinv
  have hqq' : q ≫ q' = 𝟙 p.Z₀ := by
    obtain ⟨_, -, huniq⟩ := p.hdesc p.π p.hπinv
    rw [huniq (q ≫ q') (show p.π ≫ (q ≫ q') = p.π by
        rw [← Category.assoc, hq, hq']),
      huniq (𝟙 p.Z₀) (show p.π ≫ 𝟙 p.Z₀ = p.π by rw [Category.comp_id])]
  have hq'q : q' ≫ q = 𝟙 _ := by
    obtain ⟨_, -, huniq⟩ := p.d.σZ.existsUnique_relQuotientπ_lift p.d.f p.d.over_base
      (p.d.σZ.relQuotientπ p.d.f p.d.over_base) hπinv₀
    rw [huniq (q' ≫ q) (show p.d.σZ.relQuotientπ p.d.f p.d.over_base ≫ (q' ≫ q) =
          p.d.σZ.relQuotientπ p.d.f p.d.over_base by
        rw [← Category.assoc, hq', hq]),
      huniq (𝟙 _) (show p.d.σZ.relQuotientπ p.d.f p.d.over_base ≫ 𝟙 _ =
          p.d.σZ.relQuotientπ p.d.f p.d.over_base by rw [Category.comp_id])]
  haveI : IsIso q := ⟨q', hqq', hq'q⟩
  -- `f₀ = q ≫ relQuotientStruct` by uniqueness of descents of `f`
  have hstruct : q ≫ p.d.σZ.relQuotientStruct p.d.f p.d.over_base = p.f₀ := by
    obtain ⟨_, -, huniq⟩ := p.hdesc p.d.f p.d.over_base
    rw [huniq (q ≫ p.d.σZ.relQuotientStruct p.d.f p.d.over_base) (show
        p.π ≫ q ≫ p.d.σZ.relQuotientStruct p.d.f p.d.over_base = p.d.f by
        rw [← Category.assoc, hq,
          p.d.σZ.relQuotientπ_comp_relQuotientStruct p.d.f p.d.over_base]),
      huniq p.f₀ p.hπf]
  obtain ⟨hFin, hEt⟩ :=
    p.d.σZ.relQuotientStruct_finite_etale_of_free p.d.f p.d.over_base
      (p.d.free_on_points hfree) p.d.finite p.d.etale
  constructor
  · rw [← hstruct, MorphismProperty.cancel_left_of_respectsIso @IsFinite]
    exact hFin
  · rw [← hstruct, MorphismProperty.cancel_left_of_respectsIso @Etale]
    exact hEt

/-- **[GHB7-3b] The base-change transport of quotient packages.** For `k : X' ⟶ X`,
the base change `pullback pX.f₀ k.baseHom` is a quotient of the pulled action
([GHB5]), so the comparison of the pulled datum with the chosen datum at `X'`
([GHB7-2a/2b], equivariant by `compare_equivariant`) descends to a canonical morphism
`q` to the chosen quotient at `X'`, characterized by `πT ≫ q = compare ≫ pX'.π` and
lying over `X'.base`. The engine of the [GHB7] functor's `map`. -/
theorem QuotPkg.exists_mapDescent {Q : ModuliProblem R} {G : Type*} [Group G]
    [Finite G] {φ : G →* Aut Q} {X X' : EllObj R} (pX : QuotPkg φ X)
    (pX' : QuotPkg φ X') (hfree : FreeAction φ)
    (k : X' ⟶ X) :
    ∃ (πT : CategoryTheory.Limits.pullback pX.d.f k.baseHom ⟶
        CategoryTheory.Limits.pullback pX.f₀ k.baseHom)
      (q : CategoryTheory.Limits.pullback pX.f₀ k.baseHom ⟶ pX'.Z₀),
      πT ≫ pullback.snd pX.f₀ k.baseHom = pullback.snd pX.d.f k.baseHom ∧
      πT ≫ pullback.fst pX.f₀ k.baseHom = pullback.fst pX.d.f k.baseHom ≫ pX.π ∧
      (∀ γ : G, (pX.d.σZ.basePullback pX.d.f pX.d.over_base k.baseHom).hom γ ≫ πT
        = πT) ∧
      (∀ {Y : Scheme.{u}} (F : CategoryTheory.Limits.pullback pX.d.f k.baseHom ⟶ Y),
        (∀ γ : G, (pX.d.σZ.basePullback pX.d.f pX.d.over_base k.baseHom).hom γ ≫ F = F) →
          ∃! q' : CategoryTheory.Limits.pullback pX.f₀ k.baseHom ⟶ Y, πT ≫ q' = F) ∧
      πT ≫ q = ((pX.d.pullback k).toRelRepData.compare pX'.d.toRelRepData).1 ≫ pX'.π ∧
      q ≫ pX'.f₀ = pullback.snd pX.f₀ k.baseHom := by
  haveI := pX.d.finite
  haveI : IsAffineHom pX.d.f := inferInstance
  -- the base-changed quotient is a quotient of the pulled action ([GHB5])
  obtain ⟨πT, hsnd, hfst, hinv, hUP⟩ :=
    AlgebraicGeometry.SchemeAction.exists_quotient_baseChange_of_free pX.d.σZ pX.d.f
      pX.d.over_base (pX.d.free_on_points hfree) pX.π pX.f₀ pX.hπf pX.hπinv pX.hdesc
      k.baseHom
  set c := ((pX.d.pullback k).toRelRepData.compare pX'.d.toRelRepData) with hc
  -- the comparison composed with the chosen projection is invariant
  have hcinv : ∀ γ : G,
      (pX.d.σZ.basePullback pX.d.f pX.d.over_base k.baseHom).hom γ ≫ (c.1 ≫ pX'.π) =
        c.1 ≫ pX'.π := by
    intro γ
    have hce : (pX.d.pullback k).σZ.hom γ ≫ c.1 = c.1 ≫ pX'.d.σZ.hom γ :=
      ModuliProblem.EquivariantRelRepData.compare_equivariant (pX.d.pullback k) pX'.d γ
    have hce' : (pX.d.σZ.basePullback pX.d.f pX.d.over_base k.baseHom).hom γ ≫ c.1 =
        c.1 ≫ pX'.d.σZ.hom γ := hce
    calc (pX.d.σZ.basePullback pX.d.f pX.d.over_base k.baseHom).hom γ ≫ (c.1 ≫ pX'.π)
        = ((pX.d.σZ.basePullback pX.d.f pX.d.over_base k.baseHom).hom γ ≫ c.1) ≫ pX'.π :=
          (Category.assoc _ _ _).symm
      _ = (c.1 ≫ pX'.d.σZ.hom γ) ≫ pX'.π := congrArg (· ≫ pX'.π) hce'
      _ = c.1 ≫ (pX'.d.σZ.hom γ ≫ pX'.π) := Category.assoc _ _ _
      _ = c.1 ≫ pX'.π := by rw [pX'.hπinv γ]
  obtain ⟨q, hq, -⟩ := hUP (c.1 ≫ pX'.π) hcinv
  -- `q` lies over `X'.base`: both sides descend `pullback.snd pX.d.f k.baseHom`
  have hqf : q ≫ pX'.f₀ = pullback.snd pX.f₀ k.baseHom := by
    obtain ⟨w, hw, hwuniq⟩ := hUP (pullback.snd pX.d.f k.baseHom) (fun γ => by
      simp only [SchemeAction.basePullback, pullback.lift_snd, Category.comp_id])
    have hπTqf : πT ≫ (q ≫ pX'.f₀) = pullback.snd pX.d.f k.baseHom := by
      have h1 : πT ≫ (q ≫ pX'.f₀) = (c.1 ≫ pX'.π) ≫ pX'.f₀ :=
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ pX'.f₀) hq)
      have h2 : (c.1 ≫ pX'.π) ≫ pX'.f₀ = c.1 ≫ pX'.d.f :=
        (Category.assoc _ _ _).trans (by rw [pX'.hπf])
      exact h1.trans (h2.trans c.2)
    rw [hwuniq (q ≫ pX'.f₀) hπTqf,
      hwuniq (pullback.snd pX.f₀ k.baseHom) hsnd]
  exact ⟨πT, q, hsnd, hfst, hinv, hUP, hq, hqf⟩

section Transport

variable {Q : ModuliProblem R} {G : Type*} [Group G] [Finite G] {φ : G →* Aut Q}

/-- The chosen base-change quotient projection for a package family ([GHB5] output,
choice-extracted; [GHB7-3c]). -/
noncomputable def QuotPkg.πT (pkg : ∀ X : EllObj R, QuotPkg φ X) (hfree : FreeAction φ) {X X' : EllObj R} (k : X' ⟶ X) :
    CategoryTheory.Limits.pullback (pkg X).d.f k.baseHom ⟶
      CategoryTheory.Limits.pullback (pkg X).f₀ k.baseHom :=
  ((pkg X).exists_mapDescent (pkg X') hfree k).choose

/-- The chosen base-change transport morphism ([GHB7-3b] output, choice-extracted). -/
noncomputable def QuotPkg.mapT (pkg : ∀ X : EllObj R, QuotPkg φ X) (hfree : FreeAction φ) {X X' : EllObj R} (k : X' ⟶ X) :
    CategoryTheory.Limits.pullback (pkg X).f₀ k.baseHom ⟶ (pkg X').Z₀ :=
  ((pkg X).exists_mapDescent (pkg X') hfree k).choose_spec.choose

/-- The defining clauses of the chosen transports. -/
theorem QuotPkg.mapT_spec (pkg : ∀ X : EllObj R, QuotPkg φ X) (hfree : FreeAction φ) {X X' : EllObj R} (k : X' ⟶ X) :
    QuotPkg.πT pkg hfree k ≫ pullback.snd (pkg X).f₀ k.baseHom =
      pullback.snd (pkg X).d.f k.baseHom ∧
    QuotPkg.πT pkg hfree k ≫ pullback.fst (pkg X).f₀ k.baseHom =
      pullback.fst (pkg X).d.f k.baseHom ≫ (pkg X).π ∧
    (∀ γ : G, ((pkg X).d.σZ.basePullback (pkg X).d.f (pkg X).d.over_base
      k.baseHom).hom γ ≫ QuotPkg.πT pkg hfree k = QuotPkg.πT pkg hfree k) ∧
    (∀ {Y : Scheme.{u}} (F : CategoryTheory.Limits.pullback (pkg X).d.f k.baseHom ⟶ Y),
      (∀ γ : G, ((pkg X).d.σZ.basePullback (pkg X).d.f (pkg X).d.over_base
        k.baseHom).hom γ ≫ F = F) →
        ∃! q' : CategoryTheory.Limits.pullback (pkg X).f₀ k.baseHom ⟶ Y,
          QuotPkg.πT pkg hfree k ≫ q' = F) ∧
    QuotPkg.πT pkg hfree k ≫ QuotPkg.mapT pkg hfree k =
      (((pkg X).d.pullback k).toRelRepData.compare (pkg X').d.toRelRepData).1 ≫
        (pkg X').π ∧
    QuotPkg.mapT pkg hfree k ≫ (pkg X').f₀ = pullback.snd (pkg X).f₀ k.baseHom :=
  ((pkg X).exists_mapDescent (pkg X') hfree k).choose_spec.choose_spec

/-- Transport of `mapT` along an equality of `Ell/R`-morphisms (the source pullback
moves with the base morphism; subst-internal, `map_eqv`-style). -/
theorem QuotPkg.mapT_congr (pkg : ∀ X : EllObj R, QuotPkg φ X) (hfree : FreeAction φ) {X X' : EllObj R} {k₁ k₂ : X' ⟶ X}
    (hk : k₁ = k₂) :
    QuotPkg.mapT pkg hfree k₁ =
      eqToHom (by rw [hk]) ≫ QuotPkg.mapT pkg hfree k₂ := by
  subst hk
  rw [eqToHom_refl, Category.id_comp]

/-- **The identity transport is the first projection** ([GHB7-3c] map-id law, via
`compare_pullback_id` and descent uniqueness). -/
theorem QuotPkg.mapT_id (pkg : ∀ X : EllObj R, QuotPkg φ X) (hfree : FreeAction φ) (X : EllObj R) :
    QuotPkg.mapT pkg hfree (𝟙 X) =
      pullback.fst (pkg X).f₀ (𝟙 X : X ⟶ X).baseHom := by
  obtain ⟨hsnd, hfst, hinv, hUP, hq, hqf⟩ := QuotPkg.mapT_spec pkg hfree (𝟙 X)
  have hbfst : ∀ γ : G, ((pkg X).d.σZ.basePullback (pkg X).d.f (pkg X).d.over_base
      (𝟙 X : X ⟶ X).baseHom).hom γ ≫ pullback.fst (pkg X).d.f (𝟙 X : X ⟶ X).baseHom =
      pullback.fst (pkg X).d.f (𝟙 X : X ⟶ X).baseHom ≫ (pkg X).d.σZ.hom γ := fun γ => by
    simp only [SchemeAction.basePullback, pullback.lift_fst]
  obtain ⟨w, hw, hwu⟩ := hUP
    (pullback.fst (pkg X).d.f (𝟙 X : X ⟶ X).baseHom ≫ (pkg X).π) (fun γ => by
      rw [← Category.assoc, hbfst γ, Category.assoc, (pkg X).hπinv γ])
  rw [hwu (QuotPkg.mapT pkg hfree (𝟙 X)) (hq.trans
      (congrArg (· ≫ (pkg X).π)
        (ModuliProblem.RelRepData.compare_pullback_id (pkg X).d.toRelRepData))),
    hwu (pullback.fst (pkg X).f₀ (𝟙 X : X ⟶ X).baseHom) hfst]

/-- **The transport cocycle** ([GHB7-3c] map-comp law): the chosen transports compose,
through any reassociation lifts with the stated projection clauses (`id'`/`e'` at the
representing-scheme level, `iQ`/`cQ` at the quotient level). Uniqueness of descents
along `πT (k₂ ≫ k₁)` + the comparison cocycle `compare_pullback_comp`. -/
theorem QuotPkg.mapT_comp (pkg : ∀ X : EllObj R, QuotPkg φ X) (hfree : FreeAction φ) {X X' X'' : EllObj R}
    (k₁ : X' ⟶ X) (k₂ : X'' ⟶ X')
    (id' : CategoryTheory.Limits.pullback (pkg X).d.f (k₂ ≫ k₁).baseHom ⟶
      CategoryTheory.Limits.pullback (pkg X).d.f k₁.baseHom)
    (hid_fst : id' ≫ pullback.fst (pkg X).d.f k₁.baseHom =
      pullback.fst (pkg X).d.f (k₂ ≫ k₁).baseHom)
    (hid_snd : id' ≫ pullback.snd (pkg X).d.f k₁.baseHom =
      pullback.snd (pkg X).d.f (k₂ ≫ k₁).baseHom ≫ k₂.baseHom)
    (e' : CategoryTheory.Limits.pullback (pkg X).d.f (k₂ ≫ k₁).baseHom ⟶
      CategoryTheory.Limits.pullback (pkg X').d.f k₂.baseHom)
    (he_fst : e' ≫ pullback.fst (pkg X').d.f k₂.baseHom =
      id' ≫ (((pkg X).d.pullback k₁).toRelRepData.compare (pkg X').d.toRelRepData).1)
    (he_snd : e' ≫ pullback.snd (pkg X').d.f k₂.baseHom =
      pullback.snd (pkg X).d.f (k₂ ≫ k₁).baseHom)
    (iQ : CategoryTheory.Limits.pullback (pkg X).f₀ (k₂ ≫ k₁).baseHom ⟶
      CategoryTheory.Limits.pullback (pkg X).f₀ k₁.baseHom)
    (hiQ_fst : iQ ≫ pullback.fst (pkg X).f₀ k₁.baseHom =
      pullback.fst (pkg X).f₀ (k₂ ≫ k₁).baseHom)
    (hiQ_snd : iQ ≫ pullback.snd (pkg X).f₀ k₁.baseHom =
      pullback.snd (pkg X).f₀ (k₂ ≫ k₁).baseHom ≫ k₂.baseHom)
    (cQ : CategoryTheory.Limits.pullback (pkg X).f₀ (k₂ ≫ k₁).baseHom ⟶
      CategoryTheory.Limits.pullback (pkg X').f₀ k₂.baseHom)
    (hcQ_fst : cQ ≫ pullback.fst (pkg X').f₀ k₂.baseHom =
      iQ ≫ QuotPkg.mapT pkg hfree k₁)
    (hcQ_snd : cQ ≫ pullback.snd (pkg X').f₀ k₂.baseHom =
      pullback.snd (pkg X).f₀ (k₂ ≫ k₁).baseHom) :
    cQ ≫ QuotPkg.mapT pkg hfree k₂ = QuotPkg.mapT pkg hfree (k₂ ≫ k₁) := by
  obtain ⟨hsnd₁, hfst₁, hinv₁, hUP₁, hq₁, hqf₁⟩ := QuotPkg.mapT_spec pkg hfree k₁
  obtain ⟨hsnd₂, hfst₂, hinv₂, hUP₂, hq₂, hqf₂⟩ := QuotPkg.mapT_spec pkg hfree k₂
  obtain ⟨hsndB, hfstB, hinvB, hUPB, hqB, hqfB⟩ :=
    QuotPkg.mapT_spec pkg hfree (k₂ ≫ k₁)
  -- square 1: the quotient-level inner reassociation descends the d-level one
  have hsq1 : QuotPkg.πT pkg hfree (k₂ ≫ k₁) ≫ iQ =
      id' ≫ QuotPkg.πT pkg hfree k₁ := by
    apply pullback.hom_ext
    · calc (QuotPkg.πT pkg hfree (k₂ ≫ k₁) ≫ iQ) ≫
            pullback.fst (pkg X).f₀ k₁.baseHom
          = QuotPkg.πT pkg hfree (k₂ ≫ k₁) ≫
            (iQ ≫ pullback.fst (pkg X).f₀ k₁.baseHom) := Category.assoc _ _ _
        _ = QuotPkg.πT pkg hfree (k₂ ≫ k₁) ≫
            pullback.fst (pkg X).f₀ (k₂ ≫ k₁).baseHom := by rw [hiQ_fst]
        _ = pullback.fst (pkg X).d.f (k₂ ≫ k₁).baseHom ≫ (pkg X).π := hfstB
        _ = (id' ≫ pullback.fst (pkg X).d.f k₁.baseHom) ≫ (pkg X).π := by rw [hid_fst]
        _ = id' ≫ (pullback.fst (pkg X).d.f k₁.baseHom ≫ (pkg X).π) :=
            Category.assoc _ _ _
        _ = id' ≫ (QuotPkg.πT pkg hfree k₁ ≫ pullback.fst (pkg X).f₀ k₁.baseHom)
            := by rw [hfst₁]
        _ = (id' ≫ QuotPkg.πT pkg hfree k₁) ≫ pullback.fst (pkg X).f₀ k₁.baseHom
            := (Category.assoc _ _ _).symm
    · calc (QuotPkg.πT pkg hfree (k₂ ≫ k₁) ≫ iQ) ≫
            pullback.snd (pkg X).f₀ k₁.baseHom
          = QuotPkg.πT pkg hfree (k₂ ≫ k₁) ≫
            (iQ ≫ pullback.snd (pkg X).f₀ k₁.baseHom) := Category.assoc _ _ _
        _ = QuotPkg.πT pkg hfree (k₂ ≫ k₁) ≫
            (pullback.snd (pkg X).f₀ (k₂ ≫ k₁).baseHom ≫ k₂.baseHom) := by
            rw [hiQ_snd]
        _ = (QuotPkg.πT pkg hfree (k₂ ≫ k₁) ≫
            pullback.snd (pkg X).f₀ (k₂ ≫ k₁).baseHom) ≫ k₂.baseHom :=
            (Category.assoc _ _ _).symm
        _ = pullback.snd (pkg X).d.f (k₂ ≫ k₁).baseHom ≫ k₂.baseHom := by rw [hsndB]
        _ = id' ≫ pullback.snd (pkg X).d.f k₁.baseHom := hid_snd.symm
        _ = id' ≫ (QuotPkg.πT pkg hfree k₁ ≫ pullback.snd (pkg X).f₀ k₁.baseHom)
            := by rw [hsnd₁]
        _ = (id' ≫ QuotPkg.πT pkg hfree k₁) ≫ pullback.snd (pkg X).f₀ k₁.baseHom
            := (Category.assoc _ _ _).symm
  -- square 2: the quotient-level reassociation descends the d-level one
  have hsq2 : QuotPkg.πT pkg hfree (k₂ ≫ k₁) ≫ cQ =
      e' ≫ QuotPkg.πT pkg hfree k₂ := by
    apply pullback.hom_ext
    · calc (QuotPkg.πT pkg hfree (k₂ ≫ k₁) ≫ cQ) ≫
            pullback.fst (pkg X').f₀ k₂.baseHom
          = QuotPkg.πT pkg hfree (k₂ ≫ k₁) ≫
            (cQ ≫ pullback.fst (pkg X').f₀ k₂.baseHom) := Category.assoc _ _ _
        _ = QuotPkg.πT pkg hfree (k₂ ≫ k₁) ≫
            (iQ ≫ QuotPkg.mapT pkg hfree k₁) := by rw [hcQ_fst]
        _ = (QuotPkg.πT pkg hfree (k₂ ≫ k₁) ≫ iQ) ≫
            QuotPkg.mapT pkg hfree k₁ := (Category.assoc _ _ _).symm
        _ = (id' ≫ QuotPkg.πT pkg hfree k₁) ≫
            QuotPkg.mapT pkg hfree k₁ := by rw [hsq1]
        _ = id' ≫ (QuotPkg.πT pkg hfree k₁ ≫ QuotPkg.mapT pkg hfree k₁)
            := Category.assoc _ _ _
        _ = id' ≫ ((((pkg X).d.pullback k₁).toRelRepData.compare
            (pkg X').d.toRelRepData).1 ≫ (pkg X').π) := by rw [hq₁]; rfl
        _ = (id' ≫ (((pkg X).d.pullback k₁).toRelRepData.compare
            (pkg X').d.toRelRepData).1) ≫ (pkg X').π := (Category.assoc _ _ _).symm
        _ = (e' ≫ pullback.fst (pkg X').d.f k₂.baseHom) ≫ (pkg X').π := by
            rw [he_fst]
        _ = e' ≫ (pullback.fst (pkg X').d.f k₂.baseHom ≫ (pkg X').π) :=
            Category.assoc _ _ _
        _ = e' ≫ (QuotPkg.πT pkg hfree k₂ ≫ pullback.fst (pkg X').f₀ k₂.baseHom)
            := by rw [hfst₂]
        _ = (e' ≫ QuotPkg.πT pkg hfree k₂) ≫ pullback.fst (pkg X').f₀ k₂.baseHom
            := (Category.assoc _ _ _).symm
    · calc (QuotPkg.πT pkg hfree (k₂ ≫ k₁) ≫ cQ) ≫
            pullback.snd (pkg X').f₀ k₂.baseHom
          = QuotPkg.πT pkg hfree (k₂ ≫ k₁) ≫
            (cQ ≫ pullback.snd (pkg X').f₀ k₂.baseHom) := Category.assoc _ _ _
        _ = QuotPkg.πT pkg hfree (k₂ ≫ k₁) ≫
            pullback.snd (pkg X).f₀ (k₂ ≫ k₁).baseHom := by rw [hcQ_snd]
        _ = pullback.snd (pkg X).d.f (k₂ ≫ k₁).baseHom := hsndB
        _ = e' ≫ pullback.snd (pkg X').d.f k₂.baseHom := he_snd.symm
        _ = e' ≫ (QuotPkg.πT pkg hfree k₂ ≫ pullback.snd (pkg X').f₀ k₂.baseHom)
            := by rw [hsnd₂]
        _ = (e' ≫ QuotPkg.πT pkg hfree k₂) ≫ pullback.snd (pkg X').f₀ k₂.baseHom
            := (Category.assoc _ _ _).symm
  -- both sides descend the composite comparison; conclude by uniqueness
  have hcinvB : ∀ γ : G, (((pkg X).d.σZ.basePullback (pkg X).d.f (pkg X).d.over_base
      (k₂ ≫ k₁).baseHom).hom γ) ≫
      ((((pkg X).d.pullback (k₂ ≫ k₁)).toRelRepData.compare
        (pkg X'').d.toRelRepData).1 ≫ (pkg X'').π) =
      (((pkg X).d.pullback (k₂ ≫ k₁)).toRelRepData.compare
        (pkg X'').d.toRelRepData).1 ≫ (pkg X'').π := by
    intro γ
    have hce : ((pkg X).d.pullback (k₂ ≫ k₁)).σZ.hom γ ≫
        ((((pkg X).d.pullback (k₂ ≫ k₁)).toRelRepData.compare
          (pkg X'').d.toRelRepData).1) =
        ((((pkg X).d.pullback (k₂ ≫ k₁)).toRelRepData.compare
          (pkg X'').d.toRelRepData).1) ≫ (pkg X'').d.σZ.hom γ :=
      ModuliProblem.EquivariantRelRepData.compare_equivariant
        ((pkg X).d.pullback (k₂ ≫ k₁)) (pkg X'').d γ
    have hce' : (((pkg X).d.σZ.basePullback (pkg X).d.f (pkg X).d.over_base
        (k₂ ≫ k₁).baseHom).hom γ) ≫
        ((((pkg X).d.pullback (k₂ ≫ k₁)).toRelRepData.compare
          (pkg X'').d.toRelRepData).1) =
        ((((pkg X).d.pullback (k₂ ≫ k₁)).toRelRepData.compare
          (pkg X'').d.toRelRepData).1) ≫ (pkg X'').d.σZ.hom γ := hce
    calc (((pkg X).d.σZ.basePullback (pkg X).d.f (pkg X).d.over_base
          (k₂ ≫ k₁).baseHom).hom γ) ≫
          ((((pkg X).d.pullback (k₂ ≫ k₁)).toRelRepData.compare
            (pkg X'').d.toRelRepData).1 ≫ (pkg X'').π)
        = ((((pkg X).d.σZ.basePullback (pkg X).d.f (pkg X).d.over_base
            (k₂ ≫ k₁).baseHom).hom γ) ≫
          ((((pkg X).d.pullback (k₂ ≫ k₁)).toRelRepData.compare
            (pkg X'').d.toRelRepData).1)) ≫ (pkg X'').π := (Category.assoc _ _ _).symm
      _ = (((((pkg X).d.pullback (k₂ ≫ k₁)).toRelRepData.compare
            (pkg X'').d.toRelRepData).1) ≫ (pkg X'').d.σZ.hom γ) ≫ (pkg X'').π :=
          congrArg (· ≫ (pkg X'').π) hce'
      _ = ((((pkg X).d.pullback (k₂ ≫ k₁)).toRelRepData.compare
            (pkg X'').d.toRelRepData).1) ≫ ((pkg X'').d.σZ.hom γ ≫ (pkg X'').π) :=
          Category.assoc _ _ _
      _ = ((((pkg X).d.pullback (k₂ ≫ k₁)).toRelRepData.compare
            (pkg X'').d.toRelRepData).1) ≫ (pkg X'').π := by rw [(pkg X'').hπinv γ]
  obtain ⟨w, hw, hwu⟩ := hUPB
    ((((pkg X).d.pullback (k₂ ≫ k₁)).toRelRepData.compare
      (pkg X'').d.toRelRepData).1 ≫ (pkg X'').π) hcinvB
  have hchase : QuotPkg.πT pkg hfree (k₂ ≫ k₁) ≫
      (cQ ≫ QuotPkg.mapT pkg hfree k₂) =
      (((pkg X).d.pullback (k₂ ≫ k₁)).toRelRepData.compare
        (pkg X'').d.toRelRepData).1 ≫ (pkg X'').π := by
    calc QuotPkg.πT pkg hfree (k₂ ≫ k₁) ≫
          (cQ ≫ QuotPkg.mapT pkg hfree k₂)
        = (QuotPkg.πT pkg hfree (k₂ ≫ k₁) ≫ cQ) ≫
          QuotPkg.mapT pkg hfree k₂ := (Category.assoc _ _ _).symm
      _ = (e' ≫ QuotPkg.πT pkg hfree k₂) ≫ QuotPkg.mapT pkg hfree k₂ :=
          congrArg (· ≫ QuotPkg.mapT pkg hfree k₂) hsq2
      _ = e' ≫ (QuotPkg.πT pkg hfree k₂ ≫ QuotPkg.mapT pkg hfree k₂) :=
          Category.assoc _ _ _
      _ = e' ≫ ((((pkg X').d.pullback k₂).toRelRepData.compare
          (pkg X'').d.toRelRepData).1 ≫ (pkg X'').π) := by rw [hq₂]; rfl
      _ = (e' ≫ (((pkg X').d.pullback k₂).toRelRepData.compare
          (pkg X'').d.toRelRepData).1) ≫ (pkg X'').π := (Category.assoc _ _ _).symm
      _ = (((pkg X).d.pullback (k₂ ≫ k₁)).toRelRepData.compare
          (pkg X'').d.toRelRepData).1 ≫ (pkg X'').π :=
          congrArg (· ≫ (pkg X'').π)
            (ModuliProblem.RelRepData.compare_pullback_comp
              (pkg X).d.toRelRepData (pkg X').d.toRelRepData (pkg X'').d.toRelRepData
              k₁ k₂ id' hid_fst hid_snd e' he_fst he_snd)
  rw [hwu (cQ ≫ QuotPkg.mapT pkg hfree k₂) hchase,
    hwu (QuotPkg.mapT pkg hfree (k₂ ≫ k₁)) hqB]

/-- **The quotient moduli problem** ([GHB7-3c], the functor): sections of the chosen
per-object quotients, with base change through the chosen transports. Functoriality is
`mapT_id`/`mapT_comp` fed with explicit reassociation lifts. -/
noncomputable def QuotPkg.quotProb (pkg : ∀ X : EllObj R, QuotPkg φ X)
    (hfree : FreeAction φ) : ModuliProblem R where
  obj Xop := { s : Xop.unop.base ⟶ (pkg Xop.unop).Z₀ //
    s ≫ (pkg Xop.unop).f₀ = 𝟙 Xop.unop.base }
  map {Xop X'op} kop := ↾fun s =>
    ⟨pullback.lift (kop.unop.baseHom ≫ s.1) (𝟙 X'op.unop.base) (by
        rw [Category.assoc, s.2, Category.comp_id, Category.id_comp]) ≫
      QuotPkg.mapT pkg hfree kop.unop, by
      rw [Category.assoc, (QuotPkg.mapT_spec pkg hfree kop.unop).2.2.2.2.2,
        pullback.lift_snd]⟩
  map_id Xop := by
    ext s
    show pullback.lift ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom ≫ s.1)
        (𝟙 Xop.unop.base) (by
          rw [Category.assoc, s.2, Category.comp_id, Category.id_comp]) ≫
      QuotPkg.mapT pkg hfree (𝟙 Xop.unop) = s.1
    rw [QuotPkg.mapT_id pkg hfree Xop.unop, pullback.lift_fst]
    show 𝟙 Xop.unop.base ≫ s.1 = s.1
    rw [Category.id_comp]
  map_comp {Xop X'op X''op} kop₁ kop₂ := by
    ext s
    -- the inner value is a section
    have hsec : (pullback.lift (kop₁.unop.baseHom ≫ s.1) (𝟙 X'op.unop.base) (by
          rw [Category.assoc, s.2, Category.comp_id, Category.id_comp]) ≫
        QuotPkg.mapT pkg hfree kop₁.unop) ≫ (pkg X'op.unop).f₀ =
        𝟙 X'op.unop.base := by
      rw [Category.assoc, (QuotPkg.mapT_spec pkg hfree kop₁.unop).2.2.2.2.2,
        pullback.lift_snd]
    show pullback.lift ((kop₂.unop ≫ kop₁.unop).baseHom ≫ s.1) (𝟙 X''op.unop.base) (by
        rw [Category.assoc, s.2, Category.comp_id, Category.id_comp]) ≫
      QuotPkg.mapT pkg hfree (kop₂.unop ≫ kop₁.unop) =
      pullback.lift (kop₂.unop.baseHom ≫
          (pullback.lift (kop₁.unop.baseHom ≫ s.1) (𝟙 X'op.unop.base) (by
            rw [Category.assoc, s.2, Category.comp_id, Category.id_comp]) ≫
          QuotPkg.mapT pkg hfree kop₁.unop)) (𝟙 X''op.unop.base) (by
          rw [Category.assoc, hsec, Category.comp_id, Category.id_comp]) ≫
      QuotPkg.mapT pkg hfree kop₂.unop
    -- the comparison bridge for the reassociation lift
    have hc₁f : (((pkg Xop.unop).d.pullback kop₁.unop).toRelRepData.compare
        (pkg X'op.unop).d.toRelRepData).1 ≫ (pkg X'op.unop).d.f =
        pullback.snd (pkg Xop.unop).d.f kop₁.unop.baseHom :=
      (((pkg Xop.unop).d.pullback kop₁.unop).toRelRepData.compare
        (pkg X'op.unop).d.toRelRepData).2
    rw [← QuotPkg.mapT_comp pkg hfree kop₁.unop kop₂.unop
      (pullback.lift (pullback.fst (pkg Xop.unop).d.f (kop₂.unop ≫ kop₁.unop).baseHom)
        (pullback.snd (pkg Xop.unop).d.f (kop₂.unop ≫ kop₁.unop).baseHom ≫
          kop₂.unop.baseHom)
        (by rw [Category.assoc]; exact pullback.condition))
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
      (pullback.lift
        ((pullback.lift (pullback.fst (pkg Xop.unop).d.f
            (kop₂.unop ≫ kop₁.unop).baseHom)
          (pullback.snd (pkg Xop.unop).d.f (kop₂.unop ≫ kop₁.unop).baseHom ≫
            kop₂.unop.baseHom)
          (by rw [Category.assoc]; exact pullback.condition)) ≫
          (((pkg Xop.unop).d.pullback kop₁.unop).toRelRepData.compare
            (pkg X'op.unop).d.toRelRepData).1)
        (pullback.snd (pkg Xop.unop).d.f (kop₂.unop ≫ kop₁.unop).baseHom)
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hc₁f).trans
          (pullback.lift_snd _ _ _))))
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
      (pullback.lift (pullback.fst (pkg Xop.unop).f₀ (kop₂.unop ≫ kop₁.unop).baseHom)
        (pullback.snd (pkg Xop.unop).f₀ (kop₂.unop ≫ kop₁.unop).baseHom ≫
          kop₂.unop.baseHom)
        (by rw [Category.assoc]; exact pullback.condition))
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
      (pullback.lift
        ((pullback.lift (pullback.fst (pkg Xop.unop).f₀
            (kop₂.unop ≫ kop₁.unop).baseHom)
          (pullback.snd (pkg Xop.unop).f₀ (kop₂.unop ≫ kop₁.unop).baseHom ≫
            kop₂.unop.baseHom)
          (by rw [Category.assoc]; exact pullback.condition)) ≫
          QuotPkg.mapT pkg hfree kop₁.unop)
        (pullback.snd (pkg Xop.unop).f₀ (kop₂.unop ≫ kop₁.unop).baseHom)
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
            (QuotPkg.mapT_spec pkg hfree kop₁.unop).2.2.2.2.2).trans
          (pullback.lift_snd _ _ _))))
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _),
      ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ← Category.assoc]
      conv_rhs => rw [← Category.assoc]
      congr 1
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.assoc,
          pullback.lift_fst]
        show (kop₂.unop.baseHom ≫ kop₁.unop.baseHom) ≫ s.1 =
          kop₂.unop.baseHom ≫ kop₁.unop.baseHom ≫ s.1
        rw [Category.assoc]
      · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
          Category.id_comp, Category.assoc, pullback.lift_snd, Category.comp_id]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]

/-- **The quotient projection** ([GHB7-4]): the natural transformation
`Q ⟶ quotProb`, sending a value to its identity-index classification composed with
the chosen quotient projection. Naturality is [GHB7-4a] + the descent square. -/
noncomputable def QuotPkg.projQ (pkg : ∀ X : EllObj R, QuotPkg φ X)
    (hfree : FreeAction φ) :
    Q ⟶ QuotPkg.quotProb pkg hfree where
  app Xop := ↾fun a =>
    ⟨(((pkg Xop.unop).d.eqv ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).symm
        (Q.map (Xop.unop.pullbackAlongπ
          ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op a)).1 ≫ (pkg Xop.unop).π,
      by
        rw [Category.assoc, (pkg Xop.unop).hπf]
        exact (((pkg Xop.unop).d.eqv
          ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).symm
          (Q.map (Xop.unop.pullbackAlongπ
            ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op a)).2⟩
  naturality {Xop X'op} kop := by
    ext a
    refine Subtype.ext ?_
    obtain ⟨hsndT, hfstT, hinvT, hUPT, hqT, hqfT⟩ :=
      QuotPkg.mapT_spec pkg hfree kop.unop
    -- the canonical classification at `X` and its lift over `X'.base`
    have hva := ((pkg Xop.unop).d.eqv
        ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).apply_symm_apply
      (Q.map (Xop.unop.pullbackAlongπ
        ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op a)
    have wℓ : (kop.unop.baseHom ≫ (((pkg Xop.unop).d.eqv
        ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).symm
        (Q.map (Xop.unop.pullbackAlongπ
          ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op a)).1) ≫
        (pkg Xop.unop).d.f = 𝟙 X'op.unop.base ≫ kop.unop.baseHom := by
      rw [Category.assoc, (((pkg Xop.unop).d.eqv
        ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).symm
        (Q.map (Xop.unop.pullbackAlongπ
          ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op a)).2,
        Category.id_comp]
      show kop.unop.baseHom ≫ 𝟙 Xop.unop.base = kop.unop.baseHom
      rw [Category.comp_id]
    -- key: the classification at `X'` is the lifted comparison composite ([GHB7-4a])
    have hkey := ((pkg X'op.unop).d.eqv
        ((𝟙 X'op.unop : X'op.unop ⟶ X'op.unop).baseHom)).injective
      (a₁ := ((pkg X'op.unop).d.eqv
        ((𝟙 X'op.unop : X'op.unop ⟶ X'op.unop).baseHom)).symm
        (Q.map (X'op.unop.pullbackAlongπ
          ((𝟙 X'op.unop : X'op.unop ⟶ X'op.unop).baseHom)).op (Q.map kop a)))
      (a₂ := ⟨(⟨pullback.lift (kop.unop.baseHom ≫ (((pkg Xop.unop).d.eqv
            ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).symm
            (Q.map (Xop.unop.pullbackAlongπ
              ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op a)).1)
            (𝟙 X'op.unop.base) wℓ, pullback.lift_snd _ _ _⟩ :
          { h : X'op.unop.base ⟶ ((pkg Xop.unop).d.pullback kop.unop).Z //
            h ≫ ((pkg Xop.unop).d.pullback kop.unop).f =
              (𝟙 X'op.unop : X'op.unop ⟶ X'op.unop).baseHom }).1 ≫
          (((pkg Xop.unop).d.pullback kop.unop).toRelRepData.compare
            (pkg X'op.unop).d.toRelRepData).1, by
        rw [Category.assoc, (((pkg Xop.unop).d.pullback
          kop.unop).toRelRepData.compare (pkg X'op.unop).d.toRelRepData).2]
        exact pullback.lift_snd _ _ _⟩)
      (by
        rw [Equiv.apply_symm_apply]
        exact (ModuliProblem.RelRepData.eqv_comp_compare_pullback_of_eqv
          (pkg Xop.unop).d.toRelRepData (pkg X'op.unop).d.toRelRepData kop.unop a
          _ _ hva _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
          (pullback.lift_snd _ _ _) _).symm)
    -- the descent square for the quotient-level lift
    have hsq : pullback.lift (kop.unop.baseHom ≫ ((((pkg Xop.unop).d.eqv
          ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).symm
          (Q.map (Xop.unop.pullbackAlongπ
            ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op a)).1 ≫
          (pkg Xop.unop).π)) (𝟙 X'op.unop.base) (by
          rw [Category.assoc,
            show ((((pkg Xop.unop).d.eqv
              ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).symm
              (Q.map (Xop.unop.pullbackAlongπ
                ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op a)).1 ≫
              (pkg Xop.unop).π) ≫ (pkg Xop.unop).f₀ = 𝟙 Xop.unop.base from by
              rw [Category.assoc, (pkg Xop.unop).hπf]
              exact (((pkg Xop.unop).d.eqv
                ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).symm
                (Q.map (Xop.unop.pullbackAlongπ
                  ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op a)).2,
            Category.comp_id, Category.id_comp]) =
        pullback.lift (kop.unop.baseHom ≫ (((pkg Xop.unop).d.eqv
          ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).symm
          (Q.map (Xop.unop.pullbackAlongπ
            ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op a)).1)
          (𝟙 X'op.unop.base) wℓ ≫ QuotPkg.πT pkg hfree kop.unop := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, hfstT, ← Category.assoc,
          ← Category.assoc, pullback.lift_fst]
      · rw [pullback.lift_snd, Category.assoc, hsndT, pullback.lift_snd]
    show (((pkg X'op.unop).d.eqv
        ((𝟙 X'op.unop : X'op.unop ⟶ X'op.unop).baseHom)).symm
        (Q.map (X'op.unop.pullbackAlongπ
          ((𝟙 X'op.unop : X'op.unop ⟶ X'op.unop).baseHom)).op (Q.map kop a))).1 ≫
        (pkg X'op.unop).π =
      pullback.lift (kop.unop.baseHom ≫ ((((pkg Xop.unop).d.eqv
          ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).symm
          (Q.map (Xop.unop.pullbackAlongπ
            ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op a)).1 ≫
          (pkg Xop.unop).π)) (𝟙 X'op.unop.base) (by
          rw [Category.assoc,
            show ((((pkg Xop.unop).d.eqv
              ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).symm
              (Q.map (Xop.unop.pullbackAlongπ
                ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op a)).1 ≫
              (pkg Xop.unop).π) ≫ (pkg Xop.unop).f₀ = 𝟙 Xop.unop.base from by
              rw [Category.assoc, (pkg Xop.unop).hπf]
              exact (((pkg Xop.unop).d.eqv
                ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).symm
                (Q.map (Xop.unop.pullbackAlongπ
                  ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op a)).2,
            Category.comp_id, Category.id_comp]) ≫
        QuotPkg.mapT pkg hfree kop.unop
    rw [show ((((pkg X'op.unop).d.eqv
        ((𝟙 X'op.unop : X'op.unop ⟶ X'op.unop).baseHom)).symm
        (Q.map (X'op.unop.pullbackAlongπ
          ((𝟙 X'op.unop : X'op.unop ⟶ X'op.unop).baseHom)).op (Q.map kop a))).1) =
      ((⟨pullback.lift (kop.unop.baseHom ≫ (((pkg Xop.unop).d.eqv
            ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).symm
            (Q.map (Xop.unop.pullbackAlongπ
              ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op a)).1)
            (𝟙 X'op.unop.base) wℓ, pullback.lift_snd _ _ _⟩ :
          { h : X'op.unop.base ⟶ ((pkg Xop.unop).d.pullback kop.unop).Z //
            h ≫ ((pkg Xop.unop).d.pullback kop.unop).f =
              (𝟙 X'op.unop : X'op.unop ⟶ X'op.unop).baseHom }).1 ≫
          (((pkg Xop.unop).d.pullback kop.unop).toRelRepData.compare
            (pkg X'op.unop).d.toRelRepData).1) from congrArg Subtype.val hkey,
      hsq, Category.assoc, Category.assoc, hqT]
    rfl

/-- **The projection coequalizes the action** ([GHB7-4], KM (Q1)-side): each `φ γ`
composed with the projection is the projection, since the identity-index
classification intertwines the action (`equivariant`) and the chosen projection kills
it (`hπinv`). -/
theorem QuotPkg.projQ_invariant (pkg : ∀ X : EllObj R, QuotPkg φ X)
    (hfree : FreeAction φ) (γ : G) :
    (φ γ).hom ≫ QuotPkg.projQ pkg hfree = QuotPkg.projQ pkg hfree := by
  ext Xop a
  refine Subtype.ext ?_
  have hmem : ((((pkg Xop.unop).d.eqv
      ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).symm
      (Q.map (Xop.unop.pullbackAlongπ
        ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op a)).1 ≫
      (pkg Xop.unop).d.σZ.hom γ⁻¹) ≫ (pkg Xop.unop).d.f =
      (𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom := by
    rw [Category.assoc, (pkg Xop.unop).d.over_base γ⁻¹]
    exact (((pkg Xop.unop).d.eqv
      ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).symm
      (Q.map (Xop.unop.pullbackAlongπ
        ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op a)).2
  have hkey := ((pkg Xop.unop).d.eqv
      ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).injective
    (a₁ := ((pkg Xop.unop).d.eqv
      ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).symm
      (Q.map (Xop.unop.pullbackAlongπ
        ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op
        ((φ γ).hom.app Xop a)))
    (a₂ := ⟨(((pkg Xop.unop).d.eqv
        ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).symm
        (Q.map (Xop.unop.pullbackAlongπ
          ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op a)).1 ≫
      (pkg Xop.unop).d.σZ.hom γ⁻¹, hmem⟩)
    (by
      rw [Equiv.apply_symm_apply]
      have hnat := NatTrans.naturality_apply (φ γ).hom
        (Xop.unop.pullbackAlongπ
          ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op a
      rw [← hnat]
      have heqv := (pkg Xop.unop).d.equivariant
        ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)
        (((pkg Xop.unop).d.eqv
          ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).symm
          (Q.map (Xop.unop.pullbackAlongπ
            ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op a)) γ⁻¹
      rw [inv_inv, Equiv.apply_symm_apply] at heqv
      exact heqv.symm)
  show (((pkg Xop.unop).d.eqv
      ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).symm
      (Q.map (Xop.unop.pullbackAlongπ
        ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op
        ((φ γ).hom.app Xop a))).1 ≫ (pkg Xop.unop).π =
    (((pkg Xop.unop).d.eqv
      ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).symm
      (Q.map (Xop.unop.pullbackAlongπ
        ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op a)).1 ≫ (pkg Xop.unop).π
  rw [congrArg Subtype.val hkey, Category.assoc, (pkg Xop.unop).hπinv γ⁻¹]

/-- **The transport along a tautological projection is an isomorphism**
([GHB7-5] enabler): both sides are quotients of canonically isomorphic data, so the
comparison-descended inverse exists by double descent uniqueness. -/
theorem QuotPkg.isIso_mapT_pullbackAlongπ (pkg : ∀ X : EllObj R, QuotPkg φ X)
    (hfree : FreeAction φ) {X' : EllObj R} {T : Scheme.{u}}
    (g : T ⟶ X'.base) :
    IsIso (QuotPkg.mapT pkg hfree (X'.pullbackAlongπ g)) := by
  obtain ⟨hsndT, hfstT, hinvT, hUPT, hqT, hqfT⟩ :=
    QuotPkg.mapT_spec pkg hfree (X'.pullbackAlongπ g)
  -- the reverse comparison composed with the base-changed projection is invariant
  have hFinv : ∀ γ : G, (pkg (X'.pullbackAlong g)).d.σZ.hom γ ≫
      (((pkg (X'.pullbackAlong g)).d.toRelRepData.compare
        ((pkg X').d.pullback (X'.pullbackAlongπ g)).toRelRepData).1 ≫
      QuotPkg.πT pkg hfree (X'.pullbackAlongπ g)) =
      ((pkg (X'.pullbackAlong g)).d.toRelRepData.compare
        ((pkg X').d.pullback (X'.pullbackAlongπ g)).toRelRepData).1 ≫
      QuotPkg.πT pkg hfree (X'.pullbackAlongπ g) := by
    intro γ
    have hce : (pkg (X'.pullbackAlong g)).d.σZ.hom γ ≫
        (((pkg (X'.pullbackAlong g)).d.toRelRepData.compare
          ((pkg X').d.pullback (X'.pullbackAlongπ g)).toRelRepData).1) =
        (((pkg (X'.pullbackAlong g)).d.toRelRepData.compare
          ((pkg X').d.pullback (X'.pullbackAlongπ g)).toRelRepData).1) ≫
        ((pkg X').d.pullback (X'.pullbackAlongπ g)).σZ.hom γ :=
      ModuliProblem.EquivariantRelRepData.compare_equivariant
        (pkg (X'.pullbackAlong g)).d ((pkg X').d.pullback (X'.pullbackAlongπ g)) γ
    have hce' : (pkg (X'.pullbackAlong g)).d.σZ.hom γ ≫
        (((pkg (X'.pullbackAlong g)).d.toRelRepData.compare
          ((pkg X').d.pullback (X'.pullbackAlongπ g)).toRelRepData).1) =
        (((pkg (X'.pullbackAlong g)).d.toRelRepData.compare
          ((pkg X').d.pullback (X'.pullbackAlongπ g)).toRelRepData).1) ≫
        ((pkg X').d.σZ.basePullback (pkg X').d.f (pkg X').d.over_base
          (X'.pullbackAlongπ g).baseHom).hom γ := hce
    calc (pkg (X'.pullbackAlong g)).d.σZ.hom γ ≫
        (((pkg (X'.pullbackAlong g)).d.toRelRepData.compare
          ((pkg X').d.pullback (X'.pullbackAlongπ g)).toRelRepData).1 ≫
        QuotPkg.πT pkg hfree (X'.pullbackAlongπ g))
        = ((pkg (X'.pullbackAlong g)).d.σZ.hom γ ≫
          (((pkg (X'.pullbackAlong g)).d.toRelRepData.compare
            ((pkg X').d.pullback (X'.pullbackAlongπ g)).toRelRepData).1)) ≫
          QuotPkg.πT pkg hfree (X'.pullbackAlongπ g) :=
          (Category.assoc _ _ _).symm
      _ = ((((pkg (X'.pullbackAlong g)).d.toRelRepData.compare
            ((pkg X').d.pullback (X'.pullbackAlongπ g)).toRelRepData).1) ≫
          ((pkg X').d.σZ.basePullback (pkg X').d.f (pkg X').d.over_base
            (X'.pullbackAlongπ g).baseHom).hom γ) ≫
          QuotPkg.πT pkg hfree (X'.pullbackAlongπ g) :=
          congrArg (· ≫ QuotPkg.πT pkg hfree (X'.pullbackAlongπ g)) hce'
      _ = (((pkg (X'.pullbackAlong g)).d.toRelRepData.compare
            ((pkg X').d.pullback (X'.pullbackAlongπ g)).toRelRepData).1) ≫
          (((pkg X').d.σZ.basePullback (pkg X').d.f (pkg X').d.over_base
            (X'.pullbackAlongπ g).baseHom).hom γ ≫
          QuotPkg.πT pkg hfree (X'.pullbackAlongπ g)) := Category.assoc _ _ _
      _ = (((pkg (X'.pullbackAlong g)).d.toRelRepData.compare
            ((pkg X').d.pullback (X'.pullbackAlongπ g)).toRelRepData).1) ≫
          QuotPkg.πT pkg hfree (X'.pullbackAlongπ g) :=
          congrArg ((((pkg (X'.pullbackAlong g)).d.toRelRepData.compare
            ((pkg X').d.pullback (X'.pullbackAlongπ g)).toRelRepData).1) ≫ ·)
            (hinvT γ)
  obtain ⟨q', hq', -⟩ := (pkg (X'.pullbackAlong g)).hdesc
    ((((pkg (X'.pullbackAlong g)).d.toRelRepData.compare
      ((pkg X').d.pullback (X'.pullbackAlongπ g)).toRelRepData).1) ≫
      QuotPkg.πT pkg hfree (X'.pullbackAlongπ g)) hFinv
  refine ⟨q', ?_, ?_⟩
  · -- `mapT ≫ q' = 𝟙`: both descend `πT` along `πT`
    obtain ⟨w, hw, hwu⟩ := hUPT (QuotPkg.πT pkg hfree (X'.pullbackAlongπ g))
      hinvT
    rw [hwu (QuotPkg.mapT pkg hfree (X'.pullbackAlongπ g) ≫ q')
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ q') hqT).trans
        ((Category.assoc _ _ _).trans
          ((congrArg ((((pkg X').d.pullback
              (X'.pullbackAlongπ g)).toRelRepData.compare
              (pkg (X'.pullbackAlong g)).d.toRelRepData).1 ≫ ·) hq').trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (· ≫ QuotPkg.πT pkg hfree (X'.pullbackAlongπ g))
                (ModuliProblem.RelRepData.compare_comp_compare _ _)).trans
                (Category.id_comp _))))))),
      hwu (𝟙 _) (Category.comp_id _)]
  · -- `q' ≫ mapT = 𝟙`: both descend the chosen projection along it
    obtain ⟨w, hw, hwu⟩ := (pkg (X'.pullbackAlong g)).hdesc
      (pkg (X'.pullbackAlong g)).π (pkg (X'.pullbackAlong g)).hπinv
    rw [hwu (q' ≫ QuotPkg.mapT pkg hfree (X'.pullbackAlongπ g))
      ((Category.assoc _ _ _).symm.trans ((congrArg
          (· ≫ QuotPkg.mapT pkg hfree (X'.pullbackAlongπ g)) hq').trans
        ((Category.assoc _ _ _).trans
          ((congrArg ((((pkg (X'.pullbackAlong g)).d.toRelRepData.compare
              ((pkg X').d.pullback
                (X'.pullbackAlongπ g)).toRelRepData).1) ≫ ·) hqT).trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (· ≫ (pkg (X'.pullbackAlong g)).π)
                (ModuliProblem.RelRepData.compare_comp_compare _ _)).trans
                (Category.id_comp _))))))),
      hwu (𝟙 _) (Category.comp_id _)]

/-- **The quotient problem is relatively representable by the chosen quotients**
([GHB7-5]; KM 7.1.3(1) + the étale conjunct): `(pkg X').Z₀` with `f₀` represents
`quotProb` relatively at `X'`, finite étale (through [GHB6]). The classifying
bijection composes the pullback universal property with the transport isomorphism
`isIso_mapT_pullbackAlongπ`; naturality is the transport cocycle. -/
noncomputable def QuotPkg.relRepDatum (pkg : ∀ X : EllObj R, QuotPkg φ X)
    (hfree : FreeAction φ) (X' : EllObj R) :
    ModuliProblem.RelRepData (QuotPkg.quotProb pkg hfree) X' := by
  have hqf : ∀ {T : Scheme.{u}} (g : T ⟶ X'.base),
      QuotPkg.mapT pkg hfree (X'.pullbackAlongπ g) ≫
        (pkg (X'.pullbackAlong g)).f₀ =
      (pullback.snd (pkg X').f₀ g :
        CategoryTheory.Limits.pullback (pkg X').f₀ g ⟶ T) :=
    fun g => (QuotPkg.mapT_spec pkg hfree (X'.pullbackAlongπ g)).2.2.2.2.2
  have hinvf : ∀ {T : Scheme.{u}} (g : T ⟶ X'.base)
      [IsIso (QuotPkg.mapT pkg hfree (X'.pullbackAlongπ g))],
      inv (QuotPkg.mapT pkg hfree (X'.pullbackAlongπ g)) ≫
        (pullback.snd (pkg X').f₀ g :
          CategoryTheory.Limits.pullback (pkg X').f₀ g ⟶ T) =
      (pkg (X'.pullbackAlong g)).f₀ := by
    intro T g _
    exact (congrArg (inv (QuotPkg.mapT pkg hfree (X'.pullbackAlongπ g)) ≫ ·)
        (hqf g).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (pkg (X'.pullbackAlong g)).f₀)
          (IsIso.inv_hom_id _)).trans (Category.id_comp _)))
  refine ⟨(pkg X').Z₀, (pkg X').f₀, fun {T} g =>
    haveI := QuotPkg.isIso_mapT_pullbackAlongπ pkg hfree (X' := X') g; {
    toFun := fun h => ⟨pullback.lift h.1 (𝟙 T)
        (h.2.trans (Category.id_comp g).symm) ≫
        QuotPkg.mapT pkg hfree (X'.pullbackAlongπ g),
      (Category.assoc _ _ _).trans ((congrArg (pullback.lift h.1 (𝟙 T)
          (h.2.trans (Category.id_comp g).symm) ≫ ·) (hqf g)).trans
        (pullback.lift_snd _ _ _))⟩
    invFun := fun s => ⟨(s.1 ≫ inv (QuotPkg.mapT pkg hfree
        (X'.pullbackAlongπ g))) ≫ pullback.fst (pkg X').f₀ g,
      (Category.assoc _ _ _).trans ((congrArg ((s.1 ≫ inv (QuotPkg.mapT pkg hfree (X'.pullbackAlongπ g))) ≫ ·) pullback.condition).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ g)
            ((Category.assoc _ _ _).trans
              ((congrArg (s.1 ≫ ·) (hinvf g)).trans s.2))).trans
            (Category.id_comp g))))⟩
    left_inv := fun h => Subtype.ext
      ((congrArg (· ≫ pullback.fst (pkg X').f₀ g)
        ((Category.assoc _ _ _).trans ((congrArg (pullback.lift h.1 (𝟙 T)
            (h.2.trans (Category.id_comp g).symm) ≫ ·)
          (IsIso.hom_inv_id (QuotPkg.mapT pkg hfree
            (X'.pullbackAlongπ g)))).trans (Category.comp_id _)))).trans
        (pullback.lift_fst _ _ _))
    right_inv := fun s => Subtype.ext
      ((congrArg (· ≫ QuotPkg.mapT pkg hfree (X'.pullbackAlongπ g))
        (pullback.hom_ext (pullback.lift_fst _ _ _)
          ((pullback.lift_snd _ _ _).trans
            ((Category.assoc _ _ _).trans
              ((congrArg (s.1 ≫ ·) (hinvf g)).trans s.2)).symm) :
          pullback.lift ((s.1 ≫ inv (QuotPkg.mapT pkg hfree
              (X'.pullbackAlongπ g))) ≫ pullback.fst (pkg X').f₀ g) (𝟙 T)
            ((Category.assoc _ _ _).trans ((congrArg ((s.1 ≫ inv (QuotPkg.mapT pkg
                hfree (X'.pullbackAlongπ g))) ≫ ·)
              pullback.condition).trans
              ((Category.assoc _ _ _).symm.trans
                ((congrArg (· ≫ g)
                  ((Category.assoc _ _ _).trans
                    ((congrArg (s.1 ≫ ·) (hinvf g)).trans s.2))).trans
                  (Category.id_comp g))))) =
          s.1 ≫ inv (QuotPkg.mapT pkg hfree (X'.pullbackAlongπ g)))).trans
        ((Category.assoc _ _ _).trans ((congrArg (s.1 ≫ ·)
          (IsIso.inv_hom_id (QuotPkg.mapT pkg hfree
            (X'.pullbackAlongπ g)))).trans (Category.comp_id _)))) }, ?_⟩
  -- naturality in `T` (the transport cocycle along the base-change triangle)
  intro T T' g k h
  refine Subtype.ext ?_
  have hsec : (pullback.lift h.1 (𝟙 T) (h.2.trans (Category.id_comp g).symm) ≫
      QuotPkg.mapT pkg hfree (X'.pullbackAlongπ g)) ≫
      (pkg (X'.pullbackAlong g)).f₀ = 𝟙 T :=
    (Category.assoc _ _ _).trans ((congrArg (pullback.lift h.1 (𝟙 T)
        (h.2.trans (Category.id_comp g).symm) ≫ ·) (hqf g)).trans
      (pullback.lift_snd _ _ _))
  have hc₁f : (((pkg X').d.pullback (X'.pullbackAlongπ g)).toRelRepData.compare
      (pkg (X'.pullbackAlong g)).d.toRelRepData).1 ≫ (pkg (X'.pullbackAlong g)).d.f =
      pullback.snd (pkg X').d.f (X'.pullbackAlongπ g).baseHom :=
    (((pkg X').d.pullback (X'.pullbackAlongπ g)).toRelRepData.compare
      (pkg (X'.pullbackAlong g)).d.toRelRepData).2
  show pullback.lift (k ≫ h.1) (𝟙 T')
      ((show (k ≫ h.1) ≫ (pkg X').f₀ = k ≫ g from by
        rw [Category.assoc, h.2]).trans (Category.id_comp (k ≫ g)).symm) ≫
      QuotPkg.mapT pkg hfree (X'.pullbackAlongπ (k ≫ g)) =
    pullback.lift (k ≫ (pullback.lift h.1 (𝟙 T)
        (h.2.trans (Category.id_comp g).symm) ≫
        QuotPkg.mapT pkg hfree (X'.pullbackAlongπ g))) (𝟙 T')
      ((show (k ≫ (pullback.lift h.1 (𝟙 T)
          (h.2.trans (Category.id_comp g).symm) ≫
          QuotPkg.mapT pkg hfree (X'.pullbackAlongπ g))) ≫
          (pkg (X'.pullbackAlong g)).f₀ = k from
        (Category.assoc _ _ _).trans
          ((congrArg (k ≫ ·) hsec).trans (Category.comp_id k))).trans
        (Category.id_comp k).symm) ≫
      QuotPkg.mapT pkg hfree (X'.pullbackAlongMap g k)
  rw [QuotPkg.mapT_congr pkg hfree
      (ModuliProblem.pullbackAlongMap_pullbackAlongπ X' g k).symm,
    show (eqToHom (by rw [(ModuliProblem.pullbackAlongMap_pullbackAlongπ
          X' g k).symm]) :
        CategoryTheory.Limits.pullback (pkg X').f₀
          (X'.pullbackAlongπ (k ≫ g)).baseHom ⟶
        CategoryTheory.Limits.pullback (pkg X').f₀
          (X'.pullbackAlongMap g k ≫ X'.pullbackAlongπ g).baseHom) =
      𝟙 _ from rfl]
  refine (congrArg (pullback.lift (k ≫ h.1) (𝟙 T')
      ((show (k ≫ h.1) ≫ (pkg X').f₀ = k ≫ g from by
        rw [Category.assoc, h.2]).trans (Category.id_comp (k ≫ g)).symm) ≫ ·)
    (Category.id_comp _)).trans ?_
  rw [← QuotPkg.mapT_comp pkg hfree (X'.pullbackAlongπ g)
      (X'.pullbackAlongMap g k)
      (pullback.lift (pullback.fst (pkg X').d.f (k ≫ g))
        (pullback.snd (pkg X').d.f (k ≫ g) ≫ k)
        (by rw [Category.assoc]; exact pullback.condition))
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
      (pullback.lift
        ((pullback.lift (pullback.fst (pkg X').d.f (k ≫ g))
          (pullback.snd (pkg X').d.f (k ≫ g) ≫ k)
          (by rw [Category.assoc]; exact pullback.condition)) ≫
          (((pkg X').d.pullback (X'.pullbackAlongπ g)).toRelRepData.compare
            (pkg (X'.pullbackAlong g)).d.toRelRepData).1)
        (pullback.snd (pkg X').d.f (k ≫ g))
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hc₁f).trans
          (pullback.lift_snd _ _ _))))
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
      (pullback.lift (pullback.fst (pkg X').f₀ (k ≫ g))
        (pullback.snd (pkg X').f₀ (k ≫ g) ≫ k)
        (by rw [Category.assoc]; exact pullback.condition))
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
      (pullback.lift
        ((pullback.lift (pullback.fst (pkg X').f₀ (k ≫ g))
          (pullback.snd (pkg X').f₀ (k ≫ g) ≫ k)
          (by rw [Category.assoc]; exact pullback.condition)) ≫
          QuotPkg.mapT pkg hfree (X'.pullbackAlongπ g))
        (pullback.snd (pkg X').f₀ (k ≫ g))
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (hqf g)).trans
          (pullback.lift_snd _ _ _))))
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)]
  refine ((Category.assoc _ _ _).symm.trans ?_)
  congr 1
  have hleg : ∀ (u : T' ⟶ CategoryTheory.Limits.pullback (pkg X').f₀ (k ≫ g)),
      u ≫ pullback.fst (pkg X').f₀ (k ≫ g) = k ≫ h.1 →
      u ≫ pullback.snd (pkg X').f₀ (k ≫ g) = 𝟙 T' →
      u ≫ pullback.lift
        ((pullback.lift (pullback.fst (pkg X').f₀ (k ≫ g))
          (pullback.snd (pkg X').f₀ (k ≫ g) ≫ k)
          (by rw [Category.assoc]; exact pullback.condition)) ≫
          QuotPkg.mapT pkg hfree (X'.pullbackAlongπ g))
        (pullback.snd (pkg X').f₀ (k ≫ g))
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (hqf g)).trans
          (pullback.lift_snd _ _ _))) =
      pullback.lift (k ≫ (pullback.lift h.1 (𝟙 T)
          (h.2.trans (Category.id_comp g).symm) ≫
          QuotPkg.mapT pkg hfree (X'.pullbackAlongπ g))) (𝟙 T')
        ((show (k ≫ (pullback.lift h.1 (𝟙 T)
            (h.2.trans (Category.id_comp g).symm) ≫
            QuotPkg.mapT pkg hfree (X'.pullbackAlongπ g))) ≫
            (pkg (X'.pullbackAlong g)).f₀ = k from
          (Category.assoc _ _ _).trans
            ((congrArg (k ≫ ·) hsec).trans (Category.comp_id k))).trans
          (Category.id_comp k).symm) := by
    intro u hu1 hu2
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ← Category.assoc]
      have hinner : u ≫ pullback.lift (pullback.fst (pkg X').f₀ (k ≫ g))
          (pullback.snd (pkg X').f₀ (k ≫ g) ≫ k)
          (by rw [Category.assoc]; exact pullback.condition) =
          k ≫ pullback.lift h.1 (𝟙 T) (h.2.trans (Category.id_comp g).symm) := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, hu1, Category.assoc,
            pullback.lift_fst]
        · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hu2,
            Category.id_comp, Category.assoc, pullback.lift_snd, Category.comp_id]
      exact (congrArg (· ≫ QuotPkg.mapT pkg hfree (X'.pullbackAlongπ g))
        hinner).trans (Category.assoc _ _ _)
    · rw [Category.assoc, pullback.lift_snd, hu2, pullback.lift_snd]
  exact hleg _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

/-- **The quotient problem is relatively representable, finite étale** ([GHB7-5];
`relRepDatum` packaged with the [GHB6]-gated conjuncts). -/
theorem QuotPkg.relRep_quotProb (pkg : ∀ X : EllObj R, QuotPkg φ X)
    (hfree : FreeAction φ) (X' : EllObj R) :
    ∃ d' : ModuliProblem.RelRepData (QuotPkg.quotProb pkg hfree) X',
      IsFinite d'.f ∧ Etale d'.f :=
  ⟨QuotPkg.relRepDatum pkg hfree X',
    ((pkg X').f₀_finite_etale hfree).1,
    ((pkg X').f₀_finite_etale hfree).2⟩

/-- **The cross-problem transport** ([GHB7-couniv-i], KM 7.1.3(1) scheme-level
content): a `G`-invariant morphism to a relatively representable problem induces, at
each object, a `G`-invariant morphism of representing schemes over the base. -/
theorem QuotPkg.exists_crossTransport {P' : ModuliProblem R} {X : EllObj R}
    (p : QuotPkg φ X) (d' : ModuliProblem.RelRepData P' X) (ν' : Q ⟶ P')
    (hν' : ∀ γ : G, (φ γ).hom ≫ ν' = ν') :
    ∃ (ν : p.d.Z ⟶ d'.Z) (hνf : ν ≫ d'.f = p.d.f),
      d'.eqv p.d.f ⟨ν, hνf⟩ =
        ν'.app (Opposite.op (X.pullbackAlong p.d.f))
          (p.d.eqv p.d.f ⟨𝟙 p.d.Z, Category.id_comp p.d.f⟩) ∧
      ∀ γ : G, p.d.σZ.hom γ ≫ ν = ν := by
  refine ⟨((d'.eqv p.d.f).symm (ν'.app (Opposite.op (X.pullbackAlong p.d.f))
      (p.d.eqv p.d.f ⟨𝟙 p.d.Z, Category.id_comp p.d.f⟩))).1,
    ((d'.eqv p.d.f).symm (ν'.app (Opposite.op (X.pullbackAlong p.d.f))
      (p.d.eqv p.d.f ⟨𝟙 p.d.Z, Category.id_comp p.d.f⟩))).2,
    (congrArg (d'.eqv p.d.f) (Subtype.eta _ _)).trans
      ((d'.eqv p.d.f).apply_symm_apply _), ?_⟩
  intro γ
  have hν := ((d'.eqv p.d.f).symm (ν'.app (Opposite.op (X.pullbackAlong p.d.f))
      (p.d.eqv p.d.f ⟨𝟙 p.d.Z, Category.id_comp p.d.f⟩))).2
  have hgs : p.d.σZ.hom γ ≫ p.d.f = p.d.f := p.d.over_base γ
  have hp1 : (p.d.σZ.hom γ ≫ ((d'.eqv p.d.f).symm
      (ν'.app (Opposite.op (X.pullbackAlong p.d.f))
        (p.d.eqv p.d.f ⟨𝟙 p.d.Z, Category.id_comp p.d.f⟩))).1) ≫ d'.f =
      p.d.σZ.hom γ ≫ p.d.f := by
    rw [Category.assoc, hν]
  refine congrArg Subtype.val ((d'.eqv p.d.f).injective
    (a₁ := ⟨_, hp1.trans hgs⟩) ?_)
  rw [Equiv.apply_symm_apply]
  -- d'-side: index-shift + naturality peel the action off
  rw [ModuliProblem.RelRepData.eqv_congr d' hgs
      (p.d.σZ.hom γ ≫ ((d'.eqv p.d.f).symm
        (ν'.app (Opposite.op (X.pullbackAlong p.d.f))
          (p.d.eqv p.d.f ⟨𝟙 p.d.Z, Category.id_comp p.d.f⟩))).1) hp1,
    d'.nat p.d.f (p.d.σZ.hom γ) ((d'.eqv p.d.f).symm
      (ν'.app (Opposite.op (X.pullbackAlong p.d.f))
        (p.d.eqv p.d.f ⟨𝟙 p.d.Z, Category.id_comp p.d.f⟩))),
    Equiv.apply_symm_apply,
    ← NatTrans.naturality_apply ν' (X.pullbackAlongMap p.d.f (p.d.σZ.hom γ)).op
      (p.d.eqv p.d.f ⟨𝟙 p.d.Z, Category.id_comp p.d.f⟩),
    ← NatTrans.naturality_apply ν'
      (eqToHom (congrArg (fun t => Opposite.op (X.pullbackAlong t)) hgs))
      (Q.map (X.pullbackAlongMap p.d.f (p.d.σZ.hom γ)).op
        (p.d.eqv p.d.f ⟨𝟙 p.d.Z, Category.id_comp p.d.f⟩))]
  -- Q-side: the transported universal element is the `γ⁻¹`-twisted one
  have hp2 : (p.d.σZ.hom γ ≫ 𝟙 p.d.Z) ≫ p.d.f = p.d.σZ.hom γ ≫ p.d.f := by
    rw [Category.comp_id]
  have hQside : Q.map (eqToHom (congrArg (fun t =>
      Opposite.op (X.pullbackAlong t)) hgs))
      (Q.map (X.pullbackAlongMap p.d.f (p.d.σZ.hom γ)).op
        (p.d.eqv p.d.f ⟨𝟙 p.d.Z, Category.id_comp p.d.f⟩)) =
      (φ γ⁻¹).hom.app (Opposite.op (X.pullbackAlong p.d.f))
        (p.d.eqv p.d.f ⟨𝟙 p.d.Z, Category.id_comp p.d.f⟩) := by
    rw [← p.d.nat p.d.f (p.d.σZ.hom γ) ⟨𝟙 p.d.Z, Category.id_comp p.d.f⟩,
      ← ModuliProblem.RelRepData.eqv_congr p.d.toRelRepData hgs
        (p.d.σZ.hom γ ≫ 𝟙 p.d.Z) hp2,
      show (⟨p.d.σZ.hom γ ≫ 𝟙 p.d.Z, hp2.trans hgs⟩ :
        { h : p.d.Z ⟶ p.d.Z // h ≫ p.d.f = p.d.f }) =
      ⟨𝟙 p.d.Z ≫ p.d.σZ.hom γ, by rw [Category.id_comp]; exact hgs⟩ from
        Subtype.ext ((Category.comp_id _).trans (Category.id_comp _).symm)]
    exact p.d.equivariant p.d.f ⟨𝟙 p.d.Z, Category.id_comp p.d.f⟩ γ
  rw [hQside,
    show ν'.app (Opposite.op (X.pullbackAlong p.d.f))
      ((φ γ⁻¹).hom.app (Opposite.op (X.pullbackAlong p.d.f))
        (p.d.eqv p.d.f ⟨𝟙 p.d.Z, Category.id_comp p.d.f⟩)) =
      ((φ γ⁻¹).hom ≫ ν').app (Opposite.op (X.pullbackAlong p.d.f))
        (p.d.eqv p.d.f ⟨𝟙 p.d.Z, Category.id_comp p.d.f⟩) from rfl,
    hν' γ⁻¹]

/-- **The descended cross-problem transport** ([GHB7-couniv-ii]): the `G`-invariant
transport descends uniquely through the chosen quotient, over the base. -/
theorem QuotPkg.exists_crossDescent {P' : ModuliProblem R} {X : EllObj R}
    (p : QuotPkg φ X) (d' : ModuliProblem.RelRepData P' X)
    (ν : p.d.Z ⟶ d'.Z) (hνf : ν ≫ d'.f = p.d.f)
    (hνinv : ∀ γ : G, p.d.σZ.hom γ ≫ ν = ν) :
    ∃ μX : p.Z₀ ⟶ d'.Z, p.π ≫ μX = ν ∧ μX ≫ d'.f = p.f₀ ∧
      ∀ μX' : p.Z₀ ⟶ d'.Z, p.π ≫ μX' = ν → μX' = μX := by
  obtain ⟨μX, hμ, huniq⟩ := p.hdesc ν hνinv
  refine ⟨μX, hμ, ?_, fun μX' h' => huniq μX' h'⟩
  -- both `μX ≫ d'.f` and `f₀` descend the invariant `p.d.f`
  obtain ⟨w, hw, hwu⟩ := p.hdesc p.d.f p.d.over_base
  rw [hwu (μX ≫ d'.f) ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ d'.f) hμ).trans hνf)),
    hwu p.f₀ p.hπf]

/-- **The cross-problem classification key** ([GHB7-couniv], the relative
`homEquiv_comp_transportHom`): composing a classifying section with the transport
classifies the `ν'`-image (GHB1's `relKey`, cross-problem). -/
theorem QuotPkg.crossRelKey {P' : ModuliProblem R} {X : EllObj R}
    (p : QuotPkg φ X) (dP : ModuliProblem.RelRepData P' X) (ν' : Q ⟶ P')
    (νX : p.d.Z ⟶ dP.Z) (hνXf : νX ≫ dP.f = p.d.f)
    (hclX : dP.eqv p.d.f ⟨νX, hνXf⟩ =
      ν'.app (Opposite.op (X.pullbackAlong p.d.f))
        (p.d.eqv p.d.f ⟨𝟙 p.d.Z, Category.id_comp p.d.f⟩))
    {T : Scheme.{u}} (g : T ⟶ X.base)
    (h : { h : T ⟶ p.d.Z // h ≫ p.d.f = g })
    (m : (h.1 ≫ νX) ≫ dP.f = g) :
    dP.eqv g ⟨h.1 ≫ νX, m⟩ =
      ν'.app (Opposite.op (X.pullbackAlong g)) (p.d.eqv g h) := by
  obtain ⟨h, hh⟩ := h
  subst hh
  have hnat := dP.nat p.d.f h ⟨νX, hνXf⟩
  rw [show (⟨h ≫ νX, m⟩ : { v : T ⟶ dP.Z // v ≫ dP.f = h ≫ p.d.f }) =
      ⟨h ≫ νX, by rw [Category.assoc, hνXf]⟩ from Subtype.ext rfl,
    hnat, hclX,
    ← NatTrans.naturality_apply ν' (X.pullbackAlongMap p.d.f h).op
      (p.d.eqv p.d.f ⟨𝟙 p.d.Z, Category.id_comp p.d.f⟩),
    ← p.d.nat p.d.f h ⟨𝟙 p.d.Z, Category.id_comp p.d.f⟩]
  exact congrArg (fun z => ν'.app (Opposite.op (X.pullbackAlong (h ≫ p.d.f)))
    (p.d.eqv (h ≫ p.d.f) z)) (Subtype.ext (Category.comp_id h))

/-- **Naturality of the cross-problem transports** ([GHB7-couniv-iii-a]): the
`ν`-transports at `X` and `X'` are intertwined by the comparison morphisms of the
pulled data on both problem sides. Clause-parameterized in the classifying properties
(`hclX`/`hclX'`) and the reassociation lift `e`. -/
theorem QuotPkg.crossTransport_natural {P' : ModuliProblem R} {X X' : EllObj R}
    (p : QuotPkg φ X) (p' : QuotPkg φ X')
    (dP : ModuliProblem.RelRepData P' X) (dP' : ModuliProblem.RelRepData P' X')
    (ν' : Q ⟶ P') (k : X' ⟶ X)
    (νX : p.d.Z ⟶ dP.Z) (hνXf : νX ≫ dP.f = p.d.f)
    (hclX : dP.eqv p.d.f ⟨νX, hνXf⟩ =
      ν'.app (Opposite.op (X.pullbackAlong p.d.f))
        (p.d.eqv p.d.f ⟨𝟙 p.d.Z, Category.id_comp p.d.f⟩))
    (νX' : p'.d.Z ⟶ dP'.Z) (hνX'f : νX' ≫ dP'.f = p'.d.f)
    (hclX' : dP'.eqv p'.d.f ⟨νX', hνX'f⟩ =
      ν'.app (Opposite.op (X'.pullbackAlong p'.d.f))
        (p'.d.eqv p'.d.f ⟨𝟙 p'.d.Z, Category.id_comp p'.d.f⟩))
    (e : CategoryTheory.Limits.pullback p.d.f k.baseHom ⟶
      CategoryTheory.Limits.pullback dP.f k.baseHom)
    (he_fst : e ≫ pullback.fst dP.f k.baseHom =
      pullback.fst p.d.f k.baseHom ≫ νX)
    (he_snd : e ≫ pullback.snd dP.f k.baseHom = pullback.snd p.d.f k.baseHom) :
    ((p.d.pullback k).toRelRepData.compare p'.d.toRelRepData).1 ≫ νX' =
      e ≫ ((dP.pullback k).compare dP').1 := by
  have hcQ2 : ((p.d.pullback k).toRelRepData.compare p'.d.toRelRepData).1 ≫
      p'.d.f = pullback.snd p.d.f k.baseHom :=
    ((p.d.pullback k).toRelRepData.compare p'.d.toRelRepData).2
  have hcP2 : ((dP.pullback k).compare dP').1 ≫ dP'.f =
      pullback.snd dP.f k.baseHom := ((dP.pullback k).compare dP').2
  have m₁ : (((p.d.pullback k).toRelRepData.compare p'.d.toRelRepData).1 ≫ νX') ≫
      dP'.f = (p.d.pullback k).f :=
    (Category.assoc _ _ _).trans
      ((congrArg (((p.d.pullback k).toRelRepData.compare
        p'.d.toRelRepData).1 ≫ ·) hνX'f).trans hcQ2)
  have m₂ : (e ≫ ((dP.pullback k).compare dP').1) ≫ dP'.f =
      (p.d.pullback k).f :=
    (Category.assoc _ _ _).trans ((congrArg (e ≫ ·) hcP2).trans he_snd)
  have hme : e ≫ (dP.pullback k).f = (p.d.pullback k).f := he_snd
  have hkey := (dP'.eqv (p.d.pullback k).f).injective
    (a₁ := ⟨((p.d.pullback k).toRelRepData.compare p'.d.toRelRepData).1 ≫ νX', m₁⟩)
    (a₂ := ⟨(⟨e, hme⟩ : { h : (p.d.pullback k).Z ⟶ (dP.pullback k).Z //
        h ≫ (dP.pullback k).f = (p.d.pullback k).f }).1 ≫
      ((dP.pullback k).compare dP').1, m₂⟩) ?_
  · exact congrArg Subtype.val hkey
  -- LHS: cross-key at X' + the Q-side comparison unfold
  have hmemc : ((p.d.pullback k).toRelRepData.compare p'.d.toRelRepData).1 ≫
      p'.d.f = (p.d.pullback k).f := hcQ2
  rw [QuotPkg.crossRelKey p' dP' ν' νX' hνX'f hclX' (p.d.pullback k).f
      ⟨((p.d.pullback k).toRelRepData.compare p'.d.toRelRepData).1, hmemc⟩ m₁,
    ModuliProblem.RelRepData.eqv_compare (p.d.pullback k).toRelRepData
      p'.d.toRelRepData]
  -- RHS: P'-side comp-compare + unfolds on both, meeting at the same iso
  have hval : ∀ (h' : { h : (p.d.pullback k).Z ⟶ (p.d.pullback k).Z //
        h ≫ (p.d.pullback k).f = (p.d.pullback k).f })
      (v : (p.d.pullback k).Z ⟶ p.d.Z)
      (hv : h'.1 ≫ pullback.fst p.d.f k.baseHom = v)
      (pv : v ≫ p.d.f = (p.d.pullback k).f ≫ k.baseHom),
      (p.d.pullback k).eqv (p.d.pullback k).f h' =
        Q.map (EllObj.toPullbackAlong
          (X'.pullbackAlongπ (p.d.pullback k).f ≫ k)).op
          (p.d.eqv ((p.d.pullback k).f ≫ k.baseHom) ⟨v, pv⟩) := by
    intro h' v hv pv; subst hv; rfl
  have hvalP : ∀ (h' : { h : (p.d.pullback k).Z ⟶ (dP.pullback k).Z //
        h ≫ (dP.pullback k).f = (p.d.pullback k).f })
      (v : (p.d.pullback k).Z ⟶ dP.Z)
      (hv : h'.1 ≫ pullback.fst dP.f k.baseHom = v)
      (pv : v ≫ dP.f = (p.d.pullback k).f ≫ k.baseHom),
      (dP.pullback k).eqv (p.d.pullback k).f h' =
        P'.map (EllObj.toPullbackAlong
          (X'.pullbackAlongπ (p.d.pullback k).f ≫ k)).op
          (dP.eqv ((p.d.pullback k).f ≫ k.baseHom) ⟨v, pv⟩) := by
    intro h' v hv pv; subst hv; rfl
  have P1 : (pullback.fst p.d.f k.baseHom ≫ p.d.f) =
      (p.d.pullback k).f ≫ k.baseHom := pullback.condition
  have P2 : (pullback.fst p.d.f k.baseHom ≫ νX) ≫ dP.f =
      (p.d.pullback k).f ≫ k.baseHom :=
    (Category.assoc _ _ _).trans
      ((congrArg (pullback.fst p.d.f k.baseHom ≫ ·) hνXf).trans
        pullback.condition)
  rw [ModuliProblem.RelRepData.eqv_comp_compare (dP.pullback k) dP'
      (p.d.pullback k).f ⟨e, hme⟩,
    hval ⟨𝟙 _, Category.id_comp _⟩ (pullback.fst p.d.f k.baseHom)
      (Category.id_comp _) P1,
    hvalP ⟨e, hme⟩ (pullback.fst p.d.f k.baseHom ≫ νX) he_fst P2,
    QuotPkg.crossRelKey p dP ν' νX hνXf hclX
      ((p.d.pullback k).f ≫ k.baseHom)
      ⟨pullback.fst p.d.f k.baseHom, P1⟩ P2]
  exact NatTrans.naturality_apply ν'
    (EllObj.toPullbackAlong (X'.pullbackAlongπ (p.d.pullback k).f ≫ k)).op
    (p.d.eqv ((p.d.pullback k).f ≫ k.baseHom)
      ⟨pullback.fst p.d.f k.baseHom, P1⟩)

/-- **The descended transports commute with base change** ([GHB7-couniv-iii-b]): the
chosen quotient transport followed by the descended cross-transport at `X'` equals the
pulled descended transport followed by the `P'`-side comparison. Descent uniqueness
along `πT` + `crossTransport_natural`. -/
theorem QuotPkg.crossDescent_mapT_square (pkg : ∀ X : EllObj R, QuotPkg φ X)
    (hfree : FreeAction φ)
    {P' : ModuliProblem R} {X X' : EllObj R}
    (dP : ModuliProblem.RelRepData P' X) (dP' : ModuliProblem.RelRepData P' X')
    (ν' : Q ⟶ P') (k : X' ⟶ X)
    (νX : (pkg X).d.Z ⟶ dP.Z) (hνXf : νX ≫ dP.f = (pkg X).d.f)
    (hclX : dP.eqv (pkg X).d.f ⟨νX, hνXf⟩ =
      ν'.app (Opposite.op (X.pullbackAlong (pkg X).d.f))
        ((pkg X).d.eqv (pkg X).d.f ⟨𝟙 (pkg X).d.Z, Category.id_comp (pkg X).d.f⟩))
    (νX' : (pkg X').d.Z ⟶ dP'.Z) (hνX'f : νX' ≫ dP'.f = (pkg X').d.f)
    (hclX' : dP'.eqv (pkg X').d.f ⟨νX', hνX'f⟩ =
      ν'.app (Opposite.op (X'.pullbackAlong (pkg X').d.f))
        ((pkg X').d.eqv (pkg X').d.f
          ⟨𝟙 (pkg X').d.Z, Category.id_comp (pkg X').d.f⟩))
    (μX : (pkg X).Z₀ ⟶ dP.Z) (hμX : (pkg X).π ≫ μX = νX)
    (hμXf : μX ≫ dP.f = (pkg X).f₀)
    (μX' : (pkg X').Z₀ ⟶ dP'.Z) (hμX' : (pkg X').π ≫ μX' = νX') :
    QuotPkg.mapT pkg hfree k ≫ μX' =
      pullback.lift (pullback.fst (pkg X).f₀ k.baseHom ≫ μX)
        (pullback.snd (pkg X).f₀ k.baseHom)
        ((Category.assoc _ _ _).trans
          ((congrArg (pullback.fst (pkg X).f₀ k.baseHom ≫ ·) hμXf).trans
            pullback.condition)) ≫
      ((dP.pullback k).compare dP').1 := by
  obtain ⟨hsndT, hfstT, hinvT, hUPT, hqT, hqfT⟩ := QuotPkg.mapT_spec pkg hfree k
  have W0 : (pullback.fst (pkg X).f₀ k.baseHom ≫ μX) ≫ dP.f =
      pullback.snd (pkg X).f₀ k.baseHom ≫ k.baseHom :=
    (Category.assoc _ _ _).trans
      ((congrArg (pullback.fst (pkg X).f₀ k.baseHom ≫ ·) hμXf).trans
        pullback.condition)
  -- both sides descend the same map along `πT`
  have hinv2 : ∀ γ : G, ((pkg X).d.σZ.basePullback (pkg X).d.f (pkg X).d.over_base
      k.baseHom).hom γ ≫ (QuotPkg.πT pkg hfree k ≫
        (QuotPkg.mapT pkg hfree k ≫ μX')) =
      QuotPkg.πT pkg hfree k ≫ (QuotPkg.mapT pkg hfree k ≫ μX') :=
    fun γ => (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (QuotPkg.mapT pkg hfree k ≫ μX')) (hinvT γ))
  obtain ⟨w, hw, hwu⟩ := hUPT (QuotPkg.πT pkg hfree k ≫
    (QuotPkg.mapT pkg hfree k ≫ μX')) hinv2
  rw [hwu (QuotPkg.mapT pkg hfree k ≫ μX') rfl,
    hwu (pullback.lift (pullback.fst (pkg X).f₀ k.baseHom ≫ μX)
      (pullback.snd (pkg X).f₀ k.baseHom) W0 ≫ ((dP.pullback k).compare dP').1) ?_]
  -- the lift-side also descends it: chase through `crossTransport_natural`
  have hsq : QuotPkg.πT pkg hfree k ≫
      pullback.lift (pullback.fst (pkg X).f₀ k.baseHom ≫ μX)
        (pullback.snd (pkg X).f₀ k.baseHom) W0 =
      pullback.lift (pullback.fst (pkg X).d.f k.baseHom ≫ νX)
        (pullback.snd (pkg X).d.f k.baseHom)
        ((Category.assoc _ _ _).trans
          ((congrArg (pullback.fst (pkg X).d.f k.baseHom ≫ ·) hνXf).trans
            pullback.condition)) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ← Category.assoc,
        hfstT, Category.assoc, hμX]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hsndT]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ ((dP.pullback k).compare dP').1) hsq).trans
      ((QuotPkg.crossTransport_natural (pkg X) (pkg X') dP dP' ν' k
          νX hνXf hclX νX' hνX'f hclX'
          (pullback.lift (pullback.fst (pkg X).d.f k.baseHom ≫ νX)
            (pullback.snd (pkg X).d.f k.baseHom)
            ((Category.assoc _ _ _).trans
              ((congrArg (pullback.fst (pkg X).d.f k.baseHom ≫ ·) hνXf).trans
                pullback.condition)))
          (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)).symm.trans
        ((congrArg ((((pkg X).d.pullback k).toRelRepData.compare
            (pkg X').d.toRelRepData).1 ≫ ·) hμX'.symm).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ μX') hqT.symm).trans (Category.assoc _ _ _))))))

/-- **The couniversal morphism** ([GHB7-couniv-iii-c]): the natural transformation
`quotProb ⟶ P'` assembled from a family of descended cross-transports. All choices
enter as clause hypotheses; naturality is `crossDescent_mapT_square` + the
`P'`-instance of the [GHB7-4a] transport. -/
noncomputable def QuotPkg.crossμ (pkg : ∀ X : EllObj R, QuotPkg φ X)
    (hfree : FreeAction φ)
    {P' : ModuliProblem R} (dP : ∀ X : EllObj R, ModuliProblem.RelRepData P' X)
    (ν' : Q ⟶ P')
    (νf : ∀ X : EllObj R, (pkg X).d.Z ⟶ (dP X).Z)
    (hνf : ∀ X : EllObj R, νf X ≫ (dP X).f = (pkg X).d.f)
    (hcl : ∀ X : EllObj R, (dP X).eqv (pkg X).d.f ⟨νf X, hνf X⟩ =
      ν'.app (Opposite.op (X.pullbackAlong (pkg X).d.f))
        ((pkg X).d.eqv (pkg X).d.f ⟨𝟙 (pkg X).d.Z, Category.id_comp (pkg X).d.f⟩))
    (μf : ∀ X : EllObj R, (pkg X).Z₀ ⟶ (dP X).Z)
    (hμ : ∀ X : EllObj R, (pkg X).π ≫ μf X = νf X)
    (hμf : ∀ X : EllObj R, μf X ≫ (dP X).f = (pkg X).f₀) :
    QuotPkg.quotProb pkg hfree ⟶ P' where
  app Xop := ↾fun s =>
    P'.map (EllObj.toPullbackAlong (𝟙 Xop.unop)).op
      ((dP Xop.unop).eqv ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)
        ⟨s.1 ≫ μf Xop.unop, by
          rw [Category.assoc, hμf Xop.unop]
          exact s.2⟩)
  naturality {Xop X'op} kop := by
    ext s
    show P'.map (EllObj.toPullbackAlong (𝟙 X'op.unop)).op
      ((dP X'op.unop).eqv ((𝟙 X'op.unop : X'op.unop ⟶ X'op.unop).baseHom)
        ⟨(pullback.lift (kop.unop.baseHom ≫ s.1) (𝟙 X'op.unop.base)
          (by rw [Category.assoc, s.2, Category.comp_id, Category.id_comp]) ≫
          QuotPkg.mapT pkg hfree kop.unop) ≫ μf X'op.unop, by
          rw [Category.assoc, hμf X'op.unop, Category.assoc,
            (QuotPkg.mapT_spec pkg hfree kop.unop).2.2.2.2.2,
            pullback.lift_snd]
          rfl⟩) =
      P'.map kop (P'.map (EllObj.toPullbackAlong (𝟙 Xop.unop)).op
        ((dP Xop.unop).eqv ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)
          ⟨s.1 ≫ μf Xop.unop, by
            rw [Category.assoc, hμf Xop.unop]
            exact s.2⟩))
    -- scheme-level: the transported section factors through the pulled descent
    have hW0 : (pullback.fst (pkg Xop.unop).f₀ kop.unop.baseHom ≫ μf Xop.unop) ≫
        (dP Xop.unop).f =
        pullback.snd (pkg Xop.unop).f₀ kop.unop.baseHom ≫ kop.unop.baseHom :=
      (Category.assoc _ _ _).trans
        ((congrArg (pullback.fst (pkg Xop.unop).f₀ kop.unop.baseHom ≫ ·)
          (hμf Xop.unop)).trans pullback.condition)
    have hsquare := QuotPkg.crossDescent_mapT_square pkg hfree
      (dP Xop.unop) (dP X'op.unop) ν' kop.unop
      (νf Xop.unop) (hνf Xop.unop) (hcl Xop.unop)
      (νf X'op.unop) (hνf X'op.unop) (hcl X'op.unop)
      (μf Xop.unop) (hμ Xop.unop) (hμf Xop.unop)
      (μf X'op.unop) (hμ X'op.unop)
    -- align the classified section through the square (whole-subtype congrArg)
    have M1 : (pullback.lift (kop.unop.baseHom ≫ s.1) (𝟙 X'op.unop.base)
        (by rw [Category.assoc, s.2, Category.comp_id, Category.id_comp]) ≫
        pullback.lift (pullback.fst (pkg Xop.unop).f₀ kop.unop.baseHom ≫
            μf Xop.unop)
          (pullback.snd (pkg Xop.unop).f₀ kop.unop.baseHom) hW0) ≫
        ((dP Xop.unop).pullback kop.unop).f =
        (𝟙 X'op.unop : X'op.unop ⟶ X'op.unop).baseHom :=
      (Category.assoc _ _ _).trans
        ((congrArg (pullback.lift (kop.unop.baseHom ≫ s.1) (𝟙 X'op.unop.base)
          (by rw [Category.assoc, s.2, Category.comp_id, Category.id_comp]) ≫ ·)
          (pullback.lift_snd _ _ _ :
            pullback.lift (pullback.fst (pkg Xop.unop).f₀ kop.unop.baseHom ≫
                μf Xop.unop)
              (pullback.snd (pkg Xop.unop).f₀ kop.unop.baseHom) hW0 ≫
              ((dP Xop.unop).pullback kop.unop).f =
            pullback.snd (pkg Xop.unop).f₀ kop.unop.baseHom)).trans
          (pullback.lift_snd _ _ _))
    have M2 : ((⟨pullback.lift (kop.unop.baseHom ≫ s.1) (𝟙 X'op.unop.base)
          (by rw [Category.assoc, s.2, Category.comp_id, Category.id_comp]) ≫
        pullback.lift (pullback.fst (pkg Xop.unop).f₀ kop.unop.baseHom ≫
            μf Xop.unop)
          (pullback.snd (pkg Xop.unop).f₀ kop.unop.baseHom) hW0, M1⟩ :
        { h : X'op.unop.base ⟶ ((dP Xop.unop).pullback kop.unop).Z //
          h ≫ ((dP Xop.unop).pullback kop.unop).f =
            (𝟙 X'op.unop : X'op.unop ⟶ X'op.unop).baseHom }).1 ≫
        (((dP Xop.unop).pullback kop.unop).compare (dP X'op.unop)).1) ≫
        (dP X'op.unop).f =
        (𝟙 X'op.unop : X'op.unop ⟶ X'op.unop).baseHom :=
      (Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·)
          ((((dP Xop.unop).pullback kop.unop).compare (dP X'op.unop)).2)).trans M1)
    rw [show ((dP X'op.unop).eqv
        ((𝟙 X'op.unop : X'op.unop ⟶ X'op.unop).baseHom))
        ⟨(pullback.lift (kop.unop.baseHom ≫ s.1) (𝟙 X'op.unop.base)
          (by rw [Category.assoc, s.2, Category.comp_id, Category.id_comp]) ≫
          QuotPkg.mapT pkg hfree kop.unop) ≫ μf X'op.unop, by
          rw [Category.assoc, hμf X'op.unop, Category.assoc,
            (QuotPkg.mapT_spec pkg hfree kop.unop).2.2.2.2.2,
            pullback.lift_snd]
          rfl⟩ =
      ((dP X'op.unop).eqv
        ((𝟙 X'op.unop : X'op.unop ⟶ X'op.unop).baseHom))
        ⟨(⟨pullback.lift (kop.unop.baseHom ≫ s.1) (𝟙 X'op.unop.base)
            (by rw [Category.assoc, s.2, Category.comp_id, Category.id_comp]) ≫
          pullback.lift (pullback.fst (pkg Xop.unop).f₀ kop.unop.baseHom ≫
              μf Xop.unop)
            (pullback.snd (pkg Xop.unop).f₀ kop.unop.baseHom) hW0, M1⟩ :
          { h : X'op.unop.base ⟶ ((dP Xop.unop).pullback kop.unop).Z //
            h ≫ ((dP Xop.unop).pullback kop.unop).f =
              (𝟙 X'op.unop : X'op.unop ⟶ X'op.unop).baseHom }).1 ≫
          (((dP Xop.unop).pullback kop.unop).compare (dP X'op.unop)).1, M2⟩ from
      congrArg _ (Subtype.ext ((Category.assoc _ _ _).trans
        ((congrArg (pullback.lift (kop.unop.baseHom ≫ s.1) (𝟙 X'op.unop.base)
          (by rw [Category.assoc, s.2, Category.comp_id, Category.id_comp]) ≫ ·)
          hsquare).trans (Category.assoc _ _ _).symm)))]
    -- apply the P'-instance of the [GHB7-4a] transport
    have h4a := ModuliProblem.RelRepData.eqv_comp_compare_pullback_of_eqv
      (dP Xop.unop) (dP X'op.unop) kop.unop
      (P'.map (EllObj.toPullbackAlong (𝟙 Xop.unop)).op
        ((dP Xop.unop).eqv ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)
          ⟨s.1 ≫ μf Xop.unop, by
            rw [Category.assoc, hμf Xop.unop]; exact s.2⟩))
      (s.1 ≫ μf Xop.unop)
      (by rw [Category.assoc, hμf Xop.unop]; exact s.2)
      (by
        rw [← FunctorToTypes.map_comp_apply, ← op_comp]
        have hππ : Xop.unop.pullbackAlongπ
            ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom) ≫
            EllObj.toPullbackAlong (𝟙 Xop.unop) =
            𝟙 (Xop.unop.pullbackAlong
              ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)) := by
          apply (EllObj.homPullbackAlongEquiv Xop.unop
            ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom) _).injective
          refine Subtype.ext (Prod.ext ?_ ?_)
          · exact (Category.assoc _ _ _).trans
              ((congrArg (Xop.unop.pullbackAlongπ
                ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom) ≫ ·)
                (EllObj.toPullbackAlong_pullbackAlongπ (𝟙 Xop.unop))).trans
                ((Category.comp_id _).trans (Category.id_comp _).symm))
          · show 𝟙 Xop.unop.base ≫ 𝟙 Xop.unop.base = 𝟙 Xop.unop.base
            rw [Category.comp_id]
        rw [hππ]
        show _ = P'.map (𝟙 (Opposite.op (Xop.unop.pullbackAlong
          ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)))) _
        rw [CategoryTheory.Functor.map_id]
        rfl)
      (pullback.lift (kop.unop.baseHom ≫ s.1) (𝟙 X'op.unop.base)
          (by rw [Category.assoc, s.2, Category.comp_id, Category.id_comp]) ≫
        pullback.lift (pullback.fst (pkg Xop.unop).f₀ kop.unop.baseHom ≫
            μf Xop.unop)
          (pullback.snd (pkg Xop.unop).f₀ kop.unop.baseHom) hW0)
      ((Category.assoc _ _ _).trans
        ((congrArg (pullback.lift (kop.unop.baseHom ≫ s.1) (𝟙 X'op.unop.base)
          (by rw [Category.assoc, s.2, Category.comp_id, Category.id_comp]) ≫ ·)
          (pullback.lift_fst _ _ _)).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ μf Xop.unop) (pullback.lift_fst _ _ _)).trans
              (Category.assoc _ _ _)))))
      ((Category.assoc _ _ _).trans
        ((congrArg (pullback.lift (kop.unop.baseHom ≫ s.1) (𝟙 X'op.unop.base)
          (by rw [Category.assoc, s.2, Category.comp_id, Category.id_comp]) ≫ ·)
          (pullback.lift_snd _ _ _)).trans (pullback.lift_snd _ _ _)))
      M1 M2
    exact (congrArg (fun y => P'.map (EllObj.toPullbackAlong (𝟙 X'op.unop)).op y)
        h4a).trans
      ((FunctorToTypes.map_comp_apply P'
          (X'op.unop.pullbackAlongπ
            ((𝟙 X'op.unop : X'op.unop ⟶ X'op.unop).baseHom)).op
          (EllObj.toPullbackAlong (𝟙 X'op.unop)).op
          (P'.map kop (P'.map (EllObj.toPullbackAlong (𝟙 Xop.unop)).op
            ((dP Xop.unop).eqv ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)
              ⟨s.1 ≫ μf Xop.unop, by
                rw [Category.assoc, hμf Xop.unop]; exact s.2⟩)))).symm.trans
        ((congrArg (fun m => P'.map m
            (P'.map kop (P'.map (EllObj.toPullbackAlong (𝟙 Xop.unop)).op
              ((dP Xop.unop).eqv ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)
                ⟨s.1 ≫ μf Xop.unop, by
                  rw [Category.assoc, hμf Xop.unop]; exact s.2⟩))))
          (show (X'op.unop.pullbackAlongπ
              ((𝟙 X'op.unop : X'op.unop ⟶ X'op.unop).baseHom)).op ≫
              (EllObj.toPullbackAlong (𝟙 X'op.unop)).op =
              𝟙 (Opposite.op X'op.unop) from
            congrArg Quiver.Hom.op
              (EllObj.toPullbackAlong_pullbackAlongπ (𝟙 X'op.unop)))).trans
          (FunctorToTypes.map_id_apply P' _)))

/-- **The couniversal factorization** ([GHB7-couniv-iv]): the couniversal morphism
factors the invariant map through the projection (KM 7.1.3(1), existence half). -/
theorem QuotPkg.projQ_crossμ (pkg : ∀ X : EllObj R, QuotPkg φ X)
    (hfree : FreeAction φ)
    {P' : ModuliProblem R} (dP : ∀ X : EllObj R, ModuliProblem.RelRepData P' X)
    (ν' : Q ⟶ P')
    (νf : ∀ X : EllObj R, (pkg X).d.Z ⟶ (dP X).Z)
    (hνf : ∀ X : EllObj R, νf X ≫ (dP X).f = (pkg X).d.f)
    (hcl : ∀ X : EllObj R, (dP X).eqv (pkg X).d.f ⟨νf X, hνf X⟩ =
      ν'.app (Opposite.op (X.pullbackAlong (pkg X).d.f))
        ((pkg X).d.eqv (pkg X).d.f ⟨𝟙 (pkg X).d.Z, Category.id_comp (pkg X).d.f⟩))
    (μf : ∀ X : EllObj R, (pkg X).Z₀ ⟶ (dP X).Z)
    (hμ : ∀ X : EllObj R, (pkg X).π ≫ μf X = νf X)
    (hμf : ∀ X : EllObj R, μf X ≫ (dP X).f = (pkg X).f₀) :
    QuotPkg.projQ pkg hfree ≫
      QuotPkg.crossμ pkg hfree dP ν' νf hνf hcl μf hμ hμf = ν' := by
  ext Xop a
  show P'.map (EllObj.toPullbackAlong (𝟙 Xop.unop)).op
    ((dP Xop.unop).eqv ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)
      ⟨((((pkg Xop.unop).d.eqv
          ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).symm
          (Q.map (Xop.unop.pullbackAlongπ
            ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op a)).1 ≫
        (pkg Xop.unop).π) ≫ μf Xop.unop, by
        rw [Category.assoc, hμf Xop.unop, Category.assoc, (pkg Xop.unop).hπf]
        exact ((((pkg Xop.unop).d.eqv
          ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).symm
          (Q.map (Xop.unop.pullbackAlongπ
            ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op a)).2)⟩) =
    ν'.app Xop a
  have hval : (((pkg Xop.unop).d.eqv
      ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).symm
      (Q.map (Xop.unop.pullbackAlongπ
        ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op a)).1 ≫
      ((pkg Xop.unop).π ≫ μf Xop.unop) =
      (((pkg Xop.unop).d.eqv
        ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).symm
        (Q.map (Xop.unop.pullbackAlongπ
          ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op a)).1 ≫ νf Xop.unop :=
    congrArg ((((pkg Xop.unop).d.eqv
      ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).symm
      (Q.map (Xop.unop.pullbackAlongπ
        ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op a)).1 ≫ ·)
      (hμ Xop.unop)
  have hm2 : ((((pkg Xop.unop).d.eqv
      ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).symm
      (Q.map (Xop.unop.pullbackAlongπ
        ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op a)).1 ≫ νf Xop.unop) ≫
      (dP Xop.unop).f = (𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom := by
    rw [Category.assoc, hνf Xop.unop]
    exact ((((pkg Xop.unop).d.eqv
      ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).symm
      (Q.map (Xop.unop.pullbackAlongπ
        ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op a)).2)
  rw [show ((dP Xop.unop).eqv ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom))
      ⟨((((pkg Xop.unop).d.eqv
          ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).symm
          (Q.map (Xop.unop.pullbackAlongπ
            ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op a)).1 ≫
        (pkg Xop.unop).π) ≫ μf Xop.unop, _⟩ =
    ((dP Xop.unop).eqv ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom))
      ⟨(((pkg Xop.unop).d.eqv
          ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).symm
          (Q.map (Xop.unop.pullbackAlongπ
            ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op a)).1 ≫
        νf Xop.unop, hm2⟩ from
    congrArg _ (Subtype.ext ((Category.assoc _ _ _).trans hval)),
    QuotPkg.crossRelKey (pkg Xop.unop) (dP Xop.unop) ν' (νf Xop.unop)
      (hνf Xop.unop) (hcl Xop.unop)
      ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)
      (((pkg Xop.unop).d.eqv
        ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).symm
        (Q.map (Xop.unop.pullbackAlongπ
          ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op a)) hm2,
    Equiv.apply_symm_apply]
  exact (NatTrans.naturality_apply ν'
      (EllObj.toPullbackAlong (𝟙 Xop.unop)).op
      (Q.map (Xop.unop.pullbackAlongπ
        ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op a)).symm.trans
    (congrArg (fun y => ν'.app Xop y)
      (((FunctorToTypes.map_comp_apply Q
        (Xop.unop.pullbackAlongπ
          ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op
        (EllObj.toPullbackAlong (𝟙 Xop.unop)).op a).symm).trans
        ((congrArg (fun m => Q.map m a)
          (show (Xop.unop.pullbackAlongπ
              ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op ≫
              (EllObj.toPullbackAlong (𝟙 Xop.unop)).op =
              𝟙 (Opposite.op Xop.unop) from
            congrArg Quiver.Hom.op
              (EllObj.toPullbackAlong_pullbackAlongπ (𝟙 Xop.unop)))).trans
          (FunctorToTypes.map_id_apply Q a))))

/-- **The source-generic classification key** ([GHB7-couniv-v-prep]): `crossRelKey`
over an arbitrary source problem — needed at source `quotProb` for the couniversal
uniqueness. -/
theorem ModuliProblem.relKey_of_classifies {S P' : ModuliProblem R} {X : EllObj R}
    (dS : ModuliProblem.RelRepData S X) (dP : ModuliProblem.RelRepData P' X)
    (ν : S ⟶ P') (t : dS.Z ⟶ dP.Z) (htf : t ≫ dP.f = dS.f)
    (hclt : dP.eqv dS.f ⟨t, htf⟩ =
      ν.app (Opposite.op (X.pullbackAlong dS.f))
        (dS.eqv dS.f ⟨𝟙 dS.Z, Category.id_comp dS.f⟩))
    {T : Scheme.{u}} (g : T ⟶ X.base)
    (h : { h : T ⟶ dS.Z // h ≫ dS.f = g })
    (m : (h.1 ≫ t) ≫ dP.f = g) :
    dP.eqv g ⟨h.1 ≫ t, m⟩ =
      ν.app (Opposite.op (X.pullbackAlong g)) (dS.eqv g h) := by
  obtain ⟨h, hh⟩ := h
  subst hh
  have hnat := dP.nat dS.f h ⟨t, htf⟩
  rw [show (⟨h ≫ t, m⟩ : { v : T ⟶ dP.Z // v ≫ dP.f = h ≫ dS.f }) =
      ⟨h ≫ t, by rw [Category.assoc, htf]⟩ from Subtype.ext rfl,
    hnat, hclt,
    ← NatTrans.naturality_apply ν (X.pullbackAlongMap dS.f h).op
      (dS.eqv dS.f ⟨𝟙 dS.Z, Category.id_comp dS.f⟩),
    ← dS.nat dS.f h ⟨𝟙 dS.Z, Category.id_comp dS.f⟩]
  exact congrArg (fun z => ν.app (Opposite.op (X.pullbackAlong (h ≫ dS.f)))
    (dS.eqv (h ≫ dS.f) z)) (Subtype.ext (Category.comp_id h))

/-- The base component of an `Ell/R` object-equality transport. -/
theorem _root_.ModularCurves.EllObj.eqToHom_baseHom {A B : EllObj R} (h : A = B) :
    (eqToHom h).baseHom = eqToHom (congrArg ModularCurves.EllObj.base h) := by
  subst h
  rfl

/-- **The chosen quotient datum classifies the projection as the projected universal
element** ([GHB7-couniv-v-a]): the compatibility between `relRepDatum`'s classifying
bijection and `projQ`, at the index of the structure map. The scheme-level content of
the couniversal uniqueness. -/
theorem QuotPkg.relRepDatum_eqv_π (pkg : ∀ X : EllObj R, QuotPkg φ X)
    (hfree : FreeAction φ) (X : EllObj R) :
    (QuotPkg.relRepDatum pkg hfree X).eqv (pkg X).d.f
      ⟨(pkg X).π, (pkg X).hπf⟩ =
    (QuotPkg.projQ pkg hfree).app
      (Opposite.op (X.pullbackAlong (pkg X).d.f))
      ((pkg X).d.eqv (pkg X).d.f ⟨𝟙 (pkg X).d.Z, Category.id_comp (pkg X).d.f⟩) := by
  obtain ⟨hsndT, hfstT, hinvT, hUPT, hqT, hqfT⟩ :=
    QuotPkg.mapT_spec pkg hfree (X.pullbackAlongπ (pkg X).d.f)
  refine Subtype.ext ?_
  show pullback.lift (pkg X).π (𝟙 (X.pullbackAlong (pkg X).d.f).base)
      (show (pkg X).π ≫ (pkg X).f₀ =
        𝟙 (X.pullbackAlong (pkg X).d.f).base ≫
          (X.pullbackAlongπ (pkg X).d.f).baseHom from
        (pkg X).hπf.trans (Category.id_comp (pkg X).d.f).symm) ≫
      QuotPkg.mapT pkg hfree (X.pullbackAlongπ (pkg X).d.f) =
    (((pkg (X.pullbackAlong (pkg X).d.f)).d.eqv
        ((𝟙 (X.pullbackAlong (pkg X).d.f) :
          X.pullbackAlong (pkg X).d.f ⟶ X.pullbackAlong (pkg X).d.f).baseHom)).symm
        (Q.map ((X.pullbackAlong (pkg X).d.f).pullbackAlongπ
          ((𝟙 (X.pullbackAlong (pkg X).d.f) :
            X.pullbackAlong (pkg X).d.f ⟶
              X.pullbackAlong (pkg X).d.f).baseHom)).op
          ((pkg X).d.eqv (pkg X).d.f
            ⟨𝟙 (pkg X).d.Z, Category.id_comp (pkg X).d.f⟩))).1 ≫
      (pkg (X.pullbackAlong (pkg X).d.f)).π
  -- factor the lifted projection through the base-changed quotient projection
  have hℓπT : pullback.lift (𝟙 (pkg X).d.Z)
      (𝟙 (X.pullbackAlong (pkg X).d.f).base)
      (show 𝟙 (pkg X).d.Z ≫ (pkg X).d.f =
        𝟙 (X.pullbackAlong (pkg X).d.f).base ≫
          (X.pullbackAlongπ (pkg X).d.f).baseHom from rfl) ≫
      QuotPkg.πT pkg hfree (X.pullbackAlongπ (pkg X).d.f) =
      pullback.lift (pkg X).π (𝟙 (X.pullbackAlong (pkg X).d.f).base)
        (show (pkg X).π ≫ (pkg X).f₀ =
          𝟙 (X.pullbackAlong (pkg X).d.f).base ≫
            (X.pullbackAlongπ (pkg X).d.f).baseHom from
          (pkg X).hπf.trans (Category.id_comp (pkg X).d.f).symm) := by
    apply pullback.hom_ext
    · rw [Category.assoc, hfstT, ← Category.assoc, pullback.lift_fst,
        Category.id_comp, pullback.lift_fst]
    · rw [Category.assoc, hsndT, pullback.lift_snd, pullback.lift_snd]
  rw [← hℓπT, Category.assoc, hqT]
  refine ((Category.assoc _ _ _).symm.trans ?_)
  congr 1
  -- key: the diagonal composed with the comparison classifies the universal element
  have memℓ : pullback.lift (𝟙 (pkg X).d.Z)
      (𝟙 (X.pullbackAlong (pkg X).d.f).base)
      (show 𝟙 (pkg X).d.Z ≫ (pkg X).d.f =
        𝟙 (X.pullbackAlong (pkg X).d.f).base ≫
          (X.pullbackAlongπ (pkg X).d.f).baseHom from rfl) ≫
      ((pkg X).d.pullback (X.pullbackAlongπ (pkg X).d.f)).f =
      (𝟙 (X.pullbackAlong (pkg X).d.f) :
        X.pullbackAlong (pkg X).d.f ⟶ X.pullbackAlong (pkg X).d.f).baseHom :=
    pullback.lift_snd _ _ _
  have hm : ((⟨pullback.lift (𝟙 (pkg X).d.Z)
      (𝟙 (X.pullbackAlong (pkg X).d.f).base)
      (show 𝟙 (pkg X).d.Z ≫ (pkg X).d.f =
        𝟙 (X.pullbackAlong (pkg X).d.f).base ≫
          (X.pullbackAlongπ (pkg X).d.f).baseHom from rfl), memℓ⟩ :
      { h : (X.pullbackAlong (pkg X).d.f).base ⟶
          ((pkg X).d.pullback (X.pullbackAlongπ (pkg X).d.f)).Z //
        h ≫ ((pkg X).d.pullback (X.pullbackAlongπ (pkg X).d.f)).f =
          (𝟙 (X.pullbackAlong (pkg X).d.f) :
            X.pullbackAlong (pkg X).d.f ⟶
              X.pullbackAlong (pkg X).d.f).baseHom }).1 ≫
      (((pkg X).d.pullback (X.pullbackAlongπ (pkg X).d.f)).toRelRepData.compare
        (pkg (X.pullbackAlong (pkg X).d.f)).d.toRelRepData).1) ≫
      (pkg (X.pullbackAlong (pkg X).d.f)).d.f =
      (𝟙 (X.pullbackAlong (pkg X).d.f) :
        X.pullbackAlong (pkg X).d.f ⟶ X.pullbackAlong (pkg X).d.f).baseHom :=
    (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·)
        ((((pkg X).d.pullback (X.pullbackAlongπ (pkg X).d.f)).toRelRepData.compare
          (pkg (X.pullbackAlong (pkg X).d.f)).d.toRelRepData).2)).trans memℓ)
  have hkey : (⟨(⟨pullback.lift (𝟙 (pkg X).d.Z)
      (𝟙 (X.pullbackAlong (pkg X).d.f).base)
      (show 𝟙 (pkg X).d.Z ≫ (pkg X).d.f =
        𝟙 (X.pullbackAlong (pkg X).d.f).base ≫
          (X.pullbackAlongπ (pkg X).d.f).baseHom from rfl), memℓ⟩ :
      { h : (X.pullbackAlong (pkg X).d.f).base ⟶
          ((pkg X).d.pullback (X.pullbackAlongπ (pkg X).d.f)).Z //
        h ≫ ((pkg X).d.pullback (X.pullbackAlongπ (pkg X).d.f)).f =
          (𝟙 (X.pullbackAlong (pkg X).d.f) :
            X.pullbackAlong (pkg X).d.f ⟶
              X.pullbackAlong (pkg X).d.f).baseHom }).1 ≫
      (((pkg X).d.pullback (X.pullbackAlongπ (pkg X).d.f)).toRelRepData.compare
        (pkg (X.pullbackAlong (pkg X).d.f)).d.toRelRepData).1, hm⟩ :
      { h : (X.pullbackAlong (pkg X).d.f).base ⟶
          (pkg (X.pullbackAlong (pkg X).d.f)).d.Z //
        h ≫ (pkg (X.pullbackAlong (pkg X).d.f)).d.f =
          (𝟙 (X.pullbackAlong (pkg X).d.f) :
            X.pullbackAlong (pkg X).d.f ⟶
              X.pullbackAlong (pkg X).d.f).baseHom }) =
      ((pkg (X.pullbackAlong (pkg X).d.f)).d.eqv
        ((𝟙 (X.pullbackAlong (pkg X).d.f) :
          X.pullbackAlong (pkg X).d.f ⟶
            X.pullbackAlong (pkg X).d.f).baseHom)).symm
        (Q.map ((X.pullbackAlong (pkg X).d.f).pullbackAlongπ
          ((𝟙 (X.pullbackAlong (pkg X).d.f) :
            X.pullbackAlong (pkg X).d.f ⟶
              X.pullbackAlong (pkg X).d.f).baseHom)).op
          ((pkg X).d.eqv (pkg X).d.f
            ⟨𝟙 (pkg X).d.Z, Category.id_comp (pkg X).d.f⟩)) := by
    apply ((pkg (X.pullbackAlong (pkg X).d.f)).d.eqv
      ((𝟙 (X.pullbackAlong (pkg X).d.f) :
        X.pullbackAlong (pkg X).d.f ⟶ X.pullbackAlong (pkg X).d.f).baseHom)).injective
    rw [Equiv.apply_symm_apply]
    have P1 : 𝟙 (pkg X).d.Z ≫ (pkg X).d.f =
        (𝟙 (X.pullbackAlong (pkg X).d.f) :
          X.pullbackAlong (pkg X).d.f ⟶ X.pullbackAlong (pkg X).d.f).baseHom ≫
          (X.pullbackAlongπ (pkg X).d.f).baseHom :=
      (Category.id_comp _).trans (Category.id_comp _).symm
    have hval : ∀ (h' : { h : (X.pullbackAlong (pkg X).d.f).base ⟶
          ((pkg X).d.pullback (X.pullbackAlongπ (pkg X).d.f)).Z //
          h ≫ ((pkg X).d.pullback (X.pullbackAlongπ (pkg X).d.f)).f =
            (𝟙 (X.pullbackAlong (pkg X).d.f) :
              X.pullbackAlong (pkg X).d.f ⟶
                X.pullbackAlong (pkg X).d.f).baseHom })
        (v : (X.pullbackAlong (pkg X).d.f).base ⟶ (pkg X).d.Z)
        (hv : h'.1 ≫ pullback.fst (pkg X).d.f
          (X.pullbackAlongπ (pkg X).d.f).baseHom = v)
        (p : v ≫ (pkg X).d.f =
          (𝟙 (X.pullbackAlong (pkg X).d.f) :
            X.pullbackAlong (pkg X).d.f ⟶ X.pullbackAlong (pkg X).d.f).baseHom ≫
            (X.pullbackAlongπ (pkg X).d.f).baseHom),
        ((pkg X).d.pullback (X.pullbackAlongπ (pkg X).d.f)).eqv
          ((𝟙 (X.pullbackAlong (pkg X).d.f) :
            X.pullbackAlong (pkg X).d.f ⟶
              X.pullbackAlong (pkg X).d.f).baseHom) h' =
          Q.map (EllObj.toPullbackAlong
            ((X.pullbackAlong (pkg X).d.f).pullbackAlongπ
              ((𝟙 (X.pullbackAlong (pkg X).d.f) :
                X.pullbackAlong (pkg X).d.f ⟶
                  X.pullbackAlong (pkg X).d.f).baseHom) ≫
              X.pullbackAlongπ (pkg X).d.f)).op
            ((pkg X).d.eqv
              ((𝟙 (X.pullbackAlong (pkg X).d.f) :
                X.pullbackAlong (pkg X).d.f ⟶
                  X.pullbackAlong (pkg X).d.f).baseHom ≫
                (X.pullbackAlongπ (pkg X).d.f).baseHom) ⟨v, p⟩) := by
      intro h' v hv p; subst hv; rfl
    have hg : ((pkg X).d.f :
        (X.pullbackAlong (pkg X).d.f).base ⟶ X.base) =
        (𝟙 (X.pullbackAlong (pkg X).d.f) :
          X.pullbackAlong (pkg X).d.f ⟶ X.pullbackAlong (pkg X).d.f).baseHom ≫
          (X.pullbackAlongπ (pkg X).d.f).baseHom :=
      (Category.id_comp _).symm
    rw [ModuliProblem.RelRepData.eqv_comp_compare
        ((pkg X).d.pullback (X.pullbackAlongπ (pkg X).d.f)).toRelRepData
        (pkg (X.pullbackAlong (pkg X).d.f)).d.toRelRepData
        ((𝟙 (X.pullbackAlong (pkg X).d.f) :
          X.pullbackAlong (pkg X).d.f ⟶ X.pullbackAlong (pkg X).d.f).baseHom)
        ⟨pullback.lift (𝟙 (pkg X).d.Z)
          (𝟙 (X.pullbackAlong (pkg X).d.f).base)
          (show 𝟙 (pkg X).d.Z ≫ (pkg X).d.f =
            𝟙 (X.pullbackAlong (pkg X).d.f).base ≫
              (X.pullbackAlongπ (pkg X).d.f).baseHom from rfl), memℓ⟩,
      hval ⟨pullback.lift (𝟙 (pkg X).d.Z)
          (𝟙 (X.pullbackAlong (pkg X).d.f).base)
          (show 𝟙 (pkg X).d.Z ≫ (pkg X).d.f =
            𝟙 (X.pullbackAlong (pkg X).d.f).base ≫
              (X.pullbackAlongπ (pkg X).d.f).baseHom from rfl), memℓ⟩
        (𝟙 (pkg X).d.Z) (pullback.lift_fst _ _ _) P1,
      ]
    -- transport the index, collapse, and meet at the tautological projection
    have hEll : (X.pullbackAlong (pkg X).d.f).pullbackAlongπ
        ((𝟙 (X.pullbackAlong (pkg X).d.f) :
          X.pullbackAlong (pkg X).d.f ⟶
            X.pullbackAlong (pkg X).d.f).baseHom) =
        EllObj.toPullbackAlong
          ((X.pullbackAlong (pkg X).d.f).pullbackAlongπ
            ((𝟙 (X.pullbackAlong (pkg X).d.f) :
              X.pullbackAlong (pkg X).d.f ⟶
                X.pullbackAlong (pkg X).d.f).baseHom) ≫
            X.pullbackAlongπ (pkg X).d.f) ≫
          eqToHom (congrArg (fun t => X.pullbackAlong t) hg.symm) := by
      apply (EllObj.homPullbackAlongEquiv X (pkg X).d.f
        ((X.pullbackAlong (pkg X).d.f).pullbackAlong
          ((𝟙 (X.pullbackAlong (pkg X).d.f) :
            X.pullbackAlong (pkg X).d.f ⟶
              X.pullbackAlong (pkg X).d.f).baseHom))).injective
      refine Subtype.ext (Prod.ext ?_ ?_)
      · exact ((Category.assoc _ _ _).trans
          ((congrArg (EllObj.toPullbackAlong
              ((X.pullbackAlong (pkg X).d.f).pullbackAlongπ
                ((𝟙 (X.pullbackAlong (pkg X).d.f) :
                  X.pullbackAlong (pkg X).d.f ⟶
                    X.pullbackAlong (pkg X).d.f).baseHom) ≫
                X.pullbackAlongπ (pkg X).d.f) ≫ ·)
            (EllObj.pullbackAlongπ_congr X hg.symm).symm).trans
            (EllObj.toPullbackAlong_pullbackAlongπ
              ((X.pullbackAlong (pkg X).d.f).pullbackAlongπ
                ((𝟙 (X.pullbackAlong (pkg X).d.f) :
                  X.pullbackAlong (pkg X).d.f ⟶
                    X.pullbackAlong (pkg X).d.f).baseHom) ≫
                X.pullbackAlongπ (pkg X).d.f)))).symm
      · exact ((congrArg (𝟙 ((X.pullbackAlong (pkg X).d.f).pullbackAlong
            ((𝟙 (X.pullbackAlong (pkg X).d.f) :
              X.pullbackAlong (pkg X).d.f ⟶
                X.pullbackAlong (pkg X).d.f).baseHom)).base ≫ ·)
            (ModularCurves.EllObj.eqToHom_baseHom
              (congrArg (fun t => X.pullbackAlong t) hg.symm))).trans
          ((congrArg (𝟙 ((X.pullbackAlong (pkg X).d.f).pullbackAlong
              ((𝟙 (X.pullbackAlong (pkg X).d.f) :
                X.pullbackAlong (pkg X).d.f ⟶
                  X.pullbackAlong (pkg X).d.f).baseHom)).base ≫ ·)
            (show (eqToHom (congrArg ModularCurves.EllObj.base
              (congrArg (fun t => X.pullbackAlong t) hg.symm)) :
              (X.pullbackAlong ((𝟙 (X.pullbackAlong (pkg X).d.f) :
                X.pullbackAlong (pkg X).d.f ⟶
                  X.pullbackAlong (pkg X).d.f).baseHom ≫
                (X.pullbackAlongπ (pkg X).d.f).baseHom)).base ⟶
              (X.pullbackAlong (pkg X).d.f).base) = 𝟙 _ from rfl)).trans
            (Category.comp_id _))).symm
    exact (congrArg (fun y => Q.map (EllObj.toPullbackAlong
        (((X.pullbackAlong (pkg X).d.f).pullbackAlongπ
          (𝟙 (X.pullbackAlong (pkg X).d.f) :
            X.pullbackAlong (pkg X).d.f ⟶
              X.pullbackAlong (pkg X).d.f).baseHom) ≫
          X.pullbackAlongπ (pkg X).d.f)).op y)
        (ModuliProblem.RelRepData.eqv_congr (pkg X).d.toRelRepData hg
          (𝟙 (pkg X).d.Z) (Category.id_comp (pkg X).d.f))).trans
      ((FunctorToTypes.map_comp_apply Q
          (eqToHom (congrArg (fun t => Opposite.op (X.pullbackAlong t)) hg))
          (EllObj.toPullbackAlong
        (((X.pullbackAlong (pkg X).d.f).pullbackAlongπ
          (𝟙 (X.pullbackAlong (pkg X).d.f) :
            X.pullbackAlong (pkg X).d.f ⟶
              X.pullbackAlong (pkg X).d.f).baseHom) ≫
          X.pullbackAlongπ (pkg X).d.f)).op
          ((pkg X).d.eqv (pkg X).d.f
        ⟨𝟙 (pkg X).d.Z, Category.id_comp (pkg X).d.f⟩)).symm.trans
        (congrArg (fun m => Q.map m ((pkg X).d.eqv (pkg X).d.f
        ⟨𝟙 (pkg X).d.Z, Category.id_comp (pkg X).d.f⟩))
          (show (eqToHom (congrArg (fun t => Opposite.op (X.pullbackAlong t)) hg)) ≫ (EllObj.toPullbackAlong
        (((X.pullbackAlong (pkg X).d.f).pullbackAlongπ
          (𝟙 (X.pullbackAlong (pkg X).d.f) :
            X.pullbackAlong (pkg X).d.f ⟶
              X.pullbackAlong (pkg X).d.f).baseHom) ≫
          X.pullbackAlongπ (pkg X).d.f)).op =
              ((X.pullbackAlong (pkg X).d.f).pullbackAlongπ
          (𝟙 (X.pullbackAlong (pkg X).d.f) :
            X.pullbackAlong (pkg X).d.f ⟶
              X.pullbackAlong (pkg X).d.f).baseHom).op from
            (congrArg (· ≫ (EllObj.toPullbackAlong
        (((X.pullbackAlong (pkg X).d.f).pullbackAlongπ
          (𝟙 (X.pullbackAlong (pkg X).d.f) :
            X.pullbackAlong (pkg X).d.f ⟶
              X.pullbackAlong (pkg X).d.f).baseHom) ≫
          X.pullbackAlongπ (pkg X).d.f)).op)
              (eqToHom_op (congrArg (fun t => X.pullbackAlong t) hg.symm))).symm.trans
              (congrArg Quiver.Hom.op hEll).symm)))
  exact congrArg Subtype.val hkey

/-- **The tautological transport of a section is its classification**
([GHB7-couniv-v-b]): pulling a `quotProb`-value back along the tautological
projection is the `relRepDatum`-classification of its underlying section. -/
theorem QuotPkg.quotProb_map_pullbackAlongπ (pkg : ∀ X : EllObj R, QuotPkg φ X)
    (hfree : FreeAction φ) (X : EllObj R)
    (s : (QuotPkg.quotProb pkg hfree).obj (Opposite.op X)) :
    (QuotPkg.quotProb pkg hfree).map
      (X.pullbackAlongπ ((𝟙 X : X ⟶ X).baseHom)).op s =
    (QuotPkg.relRepDatum pkg hfree X).eqv ((𝟙 X : X ⟶ X).baseHom)
      ⟨s.1, s.2.trans rfl⟩ := by
  refine Subtype.ext ?_
  refine congrArg (· ≫ QuotPkg.mapT pkg hfree
    (X.pullbackAlongπ ((𝟙 X : X ⟶ X).baseHom))) (pullback.hom_ext ?_ ?_)
  · exact (pullback.lift_fst _ _ _).trans
      ((Category.id_comp s.1).trans (pullback.lift_fst _ _ _).symm)
  · exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm

/-- **Uniqueness of the couniversal morphism** ([GHB7-couniv-v], KM 7.1.3(1)
uniqueness half): any factorization of `ν'` through the projection agrees with
`crossμ`. Scheme-level: the induced transport descends `νf` along the chosen
quotient, so descent uniqueness pins it to `μf`; the pointwise values follow through
`relKey_of_classifies` and the tautological roundtrip. -/
theorem QuotPkg.crossμ_unique (pkg : ∀ X : EllObj R, QuotPkg φ X)
    (hfree : FreeAction φ)
    {P' : ModuliProblem R} (dP : ∀ X : EllObj R, ModuliProblem.RelRepData P' X)
    (ν' : Q ⟶ P')
    (νf : ∀ X : EllObj R, (pkg X).d.Z ⟶ (dP X).Z)
    (hνf : ∀ X : EllObj R, νf X ≫ (dP X).f = (pkg X).d.f)
    (hcl : ∀ X : EllObj R, (dP X).eqv (pkg X).d.f ⟨νf X, hνf X⟩ =
      ν'.app (Opposite.op (X.pullbackAlong (pkg X).d.f))
        ((pkg X).d.eqv (pkg X).d.f ⟨𝟙 (pkg X).d.Z, Category.id_comp (pkg X).d.f⟩))
    (hνinv : ∀ (X : EllObj R) (γ : G), (pkg X).d.σZ.hom γ ≫ νf X = νf X)
    (μf : ∀ X : EllObj R, (pkg X).Z₀ ⟶ (dP X).Z)
    (hμ : ∀ X : EllObj R, (pkg X).π ≫ μf X = νf X)
    (hμf : ∀ X : EllObj R, μf X ≫ (dP X).f = (pkg X).f₀)
    (μ'' : QuotPkg.quotProb pkg hfree ⟶ P')
    (hfact : QuotPkg.projQ pkg hfree ≫ μ'' = ν') :
    μ'' = QuotPkg.crossμ pkg hfree dP ν' νf hνf hcl μf hμ hμf := by
  ext Xop s
  -- the induced transport at this object and its classifying property
  have hclt : (dP Xop.unop).eqv (QuotPkg.relRepDatum pkg hfree Xop.unop).f
      ⟨(((dP Xop.unop).eqv
          (QuotPkg.relRepDatum pkg hfree Xop.unop).f).symm
          (μ''.app (Opposite.op (Xop.unop.pullbackAlong
            (QuotPkg.relRepDatum pkg hfree Xop.unop).f))
            ((QuotPkg.relRepDatum pkg hfree Xop.unop).eqv
              (QuotPkg.relRepDatum pkg hfree Xop.unop).f
              ⟨𝟙 (QuotPkg.relRepDatum pkg hfree Xop.unop).Z,
                Category.id_comp _⟩))).1,
        (((dP Xop.unop).eqv
          (QuotPkg.relRepDatum pkg hfree Xop.unop).f).symm
          (μ''.app (Opposite.op (Xop.unop.pullbackAlong
            (QuotPkg.relRepDatum pkg hfree Xop.unop).f))
            ((QuotPkg.relRepDatum pkg hfree Xop.unop).eqv
              (QuotPkg.relRepDatum pkg hfree Xop.unop).f
              ⟨𝟙 (QuotPkg.relRepDatum pkg hfree Xop.unop).Z,
                Category.id_comp _⟩))).2⟩ =
      μ''.app (Opposite.op (Xop.unop.pullbackAlong
        (QuotPkg.relRepDatum pkg hfree Xop.unop).f))
        ((QuotPkg.relRepDatum pkg hfree Xop.unop).eqv
          (QuotPkg.relRepDatum pkg hfree Xop.unop).f
          ⟨𝟙 (QuotPkg.relRepDatum pkg hfree Xop.unop).Z,
            Category.id_comp _⟩) :=
    (congrArg ((dP Xop.unop).eqv
        (QuotPkg.relRepDatum pkg hfree Xop.unop).f) (Subtype.eta _ _)).trans
      (((dP Xop.unop).eqv
        (QuotPkg.relRepDatum pkg hfree Xop.unop).f).apply_symm_apply _)
  -- STEP 1: the transport descends `νf` along the chosen projection
  have m₁ : ((pkg Xop.unop).π ≫ (((dP Xop.unop).eqv
          (QuotPkg.relRepDatum pkg hfree Xop.unop).f).symm
          (μ''.app (Opposite.op (Xop.unop.pullbackAlong
            (QuotPkg.relRepDatum pkg hfree Xop.unop).f))
            ((QuotPkg.relRepDatum pkg hfree Xop.unop).eqv
              (QuotPkg.relRepDatum pkg hfree Xop.unop).f
              ⟨𝟙 (QuotPkg.relRepDatum pkg hfree Xop.unop).Z,
                Category.id_comp _⟩))).1) ≫ (dP Xop.unop).f = (pkg Xop.unop).d.f :=
    (Category.assoc _ _ _).trans
      ((congrArg ((pkg Xop.unop).π ≫ ·) (((dP Xop.unop).eqv
          (QuotPkg.relRepDatum pkg hfree Xop.unop).f).symm
          (μ''.app (Opposite.op (Xop.unop.pullbackAlong
            (QuotPkg.relRepDatum pkg hfree Xop.unop).f))
            ((QuotPkg.relRepDatum pkg hfree Xop.unop).eqv
              (QuotPkg.relRepDatum pkg hfree Xop.unop).f
              ⟨𝟙 (QuotPkg.relRepDatum pkg hfree Xop.unop).Z,
                Category.id_comp _⟩))).2).trans (pkg Xop.unop).hπf)
  have h1 : (pkg Xop.unop).π ≫ (((dP Xop.unop).eqv
          (QuotPkg.relRepDatum pkg hfree Xop.unop).f).symm
          (μ''.app (Opposite.op (Xop.unop.pullbackAlong
            (QuotPkg.relRepDatum pkg hfree Xop.unop).f))
            ((QuotPkg.relRepDatum pkg hfree Xop.unop).eqv
              (QuotPkg.relRepDatum pkg hfree Xop.unop).f
              ⟨𝟙 (QuotPkg.relRepDatum pkg hfree Xop.unop).Z,
                Category.id_comp _⟩))).1 = νf Xop.unop := by
    have hkey := ((dP Xop.unop).eqv (pkg Xop.unop).d.f).injective
      (a₁ := ⟨(⟨(pkg Xop.unop).π, (pkg Xop.unop).hπf⟩ :
        { h : (pkg Xop.unop).d.Z ⟶ (QuotPkg.relRepDatum pkg hfree Xop.unop).Z //
          h ≫ (QuotPkg.relRepDatum pkg hfree Xop.unop).f = (pkg Xop.unop).d.f }).1 ≫ (((dP Xop.unop).eqv
          (QuotPkg.relRepDatum pkg hfree Xop.unop).f).symm
          (μ''.app (Opposite.op (Xop.unop.pullbackAlong
            (QuotPkg.relRepDatum pkg hfree Xop.unop).f))
            ((QuotPkg.relRepDatum pkg hfree Xop.unop).eqv
              (QuotPkg.relRepDatum pkg hfree Xop.unop).f
              ⟨𝟙 (QuotPkg.relRepDatum pkg hfree Xop.unop).Z,
                Category.id_comp _⟩))).1, m₁⟩)
      (a₂ := ⟨νf Xop.unop, hνf Xop.unop⟩) ?_
    · exact congrArg Subtype.val hkey
    rw [ModuliProblem.relKey_of_classifies
        (QuotPkg.relRepDatum pkg hfree Xop.unop)
        (dP Xop.unop) μ'' (((dP Xop.unop).eqv
          (QuotPkg.relRepDatum pkg hfree Xop.unop).f).symm
          (μ''.app (Opposite.op (Xop.unop.pullbackAlong
            (QuotPkg.relRepDatum pkg hfree Xop.unop).f))
            ((QuotPkg.relRepDatum pkg hfree Xop.unop).eqv
              (QuotPkg.relRepDatum pkg hfree Xop.unop).f
              ⟨𝟙 (QuotPkg.relRepDatum pkg hfree Xop.unop).Z,
                Category.id_comp _⟩))).1 (((dP Xop.unop).eqv
          (QuotPkg.relRepDatum pkg hfree Xop.unop).f).symm
          (μ''.app (Opposite.op (Xop.unop.pullbackAlong
            (QuotPkg.relRepDatum pkg hfree Xop.unop).f))
            ((QuotPkg.relRepDatum pkg hfree Xop.unop).eqv
              (QuotPkg.relRepDatum pkg hfree Xop.unop).f
              ⟨𝟙 (QuotPkg.relRepDatum pkg hfree Xop.unop).Z,
                Category.id_comp _⟩))).2 hclt (pkg Xop.unop).d.f
        ⟨(pkg Xop.unop).π, (pkg Xop.unop).hπf⟩ m₁,
      QuotPkg.relRepDatum_eqv_π pkg hfree Xop.unop,
      show μ''.app (Opposite.op (Xop.unop.pullbackAlong (pkg Xop.unop).d.f))
          ((QuotPkg.projQ pkg hfree).app
            (Opposite.op (Xop.unop.pullbackAlong (pkg Xop.unop).d.f))
            ((pkg Xop.unop).d.eqv (pkg Xop.unop).d.f
              ⟨𝟙 (pkg Xop.unop).d.Z, Category.id_comp (pkg Xop.unop).d.f⟩)) =
        ((QuotPkg.projQ pkg hfree ≫ μ'').app
          (Opposite.op (Xop.unop.pullbackAlong (pkg Xop.unop).d.f)))
          ((pkg Xop.unop).d.eqv (pkg Xop.unop).d.f
            ⟨𝟙 (pkg Xop.unop).d.Z, Category.id_comp (pkg Xop.unop).d.f⟩) from rfl,
      hfact, hcl Xop.unop]
  -- STEP 2: descent uniqueness pins the transport to `μf`
  have h2 : (((dP Xop.unop).eqv
          (QuotPkg.relRepDatum pkg hfree Xop.unop).f).symm
          (μ''.app (Opposite.op (Xop.unop.pullbackAlong
            (QuotPkg.relRepDatum pkg hfree Xop.unop).f))
            ((QuotPkg.relRepDatum pkg hfree Xop.unop).eqv
              (QuotPkg.relRepDatum pkg hfree Xop.unop).f
              ⟨𝟙 (QuotPkg.relRepDatum pkg hfree Xop.unop).Z,
                Category.id_comp _⟩))).1 = μf Xop.unop := by
    obtain ⟨w, hw, hwu⟩ := (pkg Xop.unop).hdesc (νf Xop.unop) (hνinv Xop.unop)
    rw [hwu (((dP Xop.unop).eqv
          (QuotPkg.relRepDatum pkg hfree Xop.unop).f).symm
          (μ''.app (Opposite.op (Xop.unop.pullbackAlong
            (QuotPkg.relRepDatum pkg hfree Xop.unop).f))
            ((QuotPkg.relRepDatum pkg hfree Xop.unop).eqv
              (QuotPkg.relRepDatum pkg hfree Xop.unop).f
              ⟨𝟙 (QuotPkg.relRepDatum pkg hfree Xop.unop).Z,
                Category.id_comp _⟩))).1 h1, hwu (μf Xop.unop) (hμ Xop.unop)]
  -- STEP 3: the pointwise value through the tautological roundtrip
  have hround : μ''.app Xop s =
      P'.map (EllObj.toPullbackAlong (𝟙 Xop.unop)).op
        (μ''.app (Opposite.op (Xop.unop.pullbackAlong
          ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)))
          ((QuotPkg.quotProb pkg hfree).map
            (Xop.unop.pullbackAlongπ
              ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op s)) := by
    rw [NatTrans.naturality_apply μ''
      (Xop.unop.pullbackAlongπ ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op s]
    exact ((FunctorToTypes.map_comp_apply P'
        (Xop.unop.pullbackAlongπ
          ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op
        (EllObj.toPullbackAlong (𝟙 Xop.unop)).op (μ''.app Xop s)).symm.trans
      ((congrArg (fun m => P'.map m (μ''.app Xop s))
        (show (Xop.unop.pullbackAlongπ
            ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)).op ≫
            (EllObj.toPullbackAlong (𝟙 Xop.unop)).op =
            𝟙 (Opposite.op Xop.unop) from
          congrArg Quiver.Hom.op
            (EllObj.toPullbackAlong_pullbackAlongπ (𝟙 Xop.unop)))).trans
        (FunctorToTypes.map_id_apply P' (μ''.app Xop s)))).symm
  have m₃ : (s.1 ≫ (((dP Xop.unop).eqv
          (QuotPkg.relRepDatum pkg hfree Xop.unop).f).symm
          (μ''.app (Opposite.op (Xop.unop.pullbackAlong
            (QuotPkg.relRepDatum pkg hfree Xop.unop).f))
            ((QuotPkg.relRepDatum pkg hfree Xop.unop).eqv
              (QuotPkg.relRepDatum pkg hfree Xop.unop).f
              ⟨𝟙 (QuotPkg.relRepDatum pkg hfree Xop.unop).Z,
                Category.id_comp _⟩))).1) ≫ (dP Xop.unop).f =
      (𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom :=
    (Category.assoc _ _ _).trans
      ((congrArg (s.1 ≫ ·) (((dP Xop.unop).eqv
          (QuotPkg.relRepDatum pkg hfree Xop.unop).f).symm
          (μ''.app (Opposite.op (Xop.unop.pullbackAlong
            (QuotPkg.relRepDatum pkg hfree Xop.unop).f))
            ((QuotPkg.relRepDatum pkg hfree Xop.unop).eqv
              (QuotPkg.relRepDatum pkg hfree Xop.unop).f
              ⟨𝟙 (QuotPkg.relRepDatum pkg hfree Xop.unop).Z,
                Category.id_comp _⟩))).2).trans (s.2.trans rfl))
  refine hround.trans ?_
  rw [QuotPkg.quotProb_map_pullbackAlongπ pkg hfree Xop.unop s,
    ← ModuliProblem.relKey_of_classifies
      (QuotPkg.relRepDatum pkg hfree Xop.unop)
      (dP Xop.unop) μ'' (((dP Xop.unop).eqv
          (QuotPkg.relRepDatum pkg hfree Xop.unop).f).symm
          (μ''.app (Opposite.op (Xop.unop.pullbackAlong
            (QuotPkg.relRepDatum pkg hfree Xop.unop).f))
            ((QuotPkg.relRepDatum pkg hfree Xop.unop).eqv
              (QuotPkg.relRepDatum pkg hfree Xop.unop).f
              ⟨𝟙 (QuotPkg.relRepDatum pkg hfree Xop.unop).Z,
                Category.id_comp _⟩))).1 (((dP Xop.unop).eqv
          (QuotPkg.relRepDatum pkg hfree Xop.unop).f).symm
          (μ''.app (Opposite.op (Xop.unop.pullbackAlong
            (QuotPkg.relRepDatum pkg hfree Xop.unop).f))
            ((QuotPkg.relRepDatum pkg hfree Xop.unop).eqv
              (QuotPkg.relRepDatum pkg hfree Xop.unop).f
              ⟨𝟙 (QuotPkg.relRepDatum pkg hfree Xop.unop).Z,
                Category.id_comp _⟩))).2 hclt
      ((𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom)
      ⟨s.1, s.2.trans rfl⟩ m₃,
    show (⟨(⟨s.1, s.2.trans rfl⟩ :
      { h : Xop.unop.base ⟶ (QuotPkg.relRepDatum pkg hfree Xop.unop).Z //
        h ≫ (QuotPkg.relRepDatum pkg hfree Xop.unop).f =
          (𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom }).1 ≫ (((dP Xop.unop).eqv
          (QuotPkg.relRepDatum pkg hfree Xop.unop).f).symm
          (μ''.app (Opposite.op (Xop.unop.pullbackAlong
            (QuotPkg.relRepDatum pkg hfree Xop.unop).f))
            ((QuotPkg.relRepDatum pkg hfree Xop.unop).eqv
              (QuotPkg.relRepDatum pkg hfree Xop.unop).f
              ⟨𝟙 (QuotPkg.relRepDatum pkg hfree Xop.unop).Z,
                Category.id_comp _⟩))).1, m₃⟩ :
      { v : Xop.unop.base ⟶ (dP Xop.unop).Z //
        v ≫ (dP Xop.unop).f =
          (𝟙 Xop.unop : Xop.unop ⟶ Xop.unop).baseHom }) =
    ⟨s.1 ≫ μf Xop.unop, by
      rw [Category.assoc, hμf Xop.unop]
      exact s.2.trans rfl⟩ from
    Subtype.ext (congrArg (s.1 ≫ ·) h2)]
  rfl

/-- The tautological projection at the identity index composed with the canonical
comparison is the identity ([GHB7-geom] enabler; the third use of this collapse). -/
theorem _root_.ModularCurves.EllObj.pullbackAlongπ_toPullbackAlong_id
    (X : EllObj R) :
    X.pullbackAlongπ ((𝟙 X : X ⟶ X).baseHom) ≫ EllObj.toPullbackAlong (𝟙 X) =
      𝟙 (X.pullbackAlong ((𝟙 X : X ⟶ X).baseHom)) := by
  apply (EllObj.homPullbackAlongEquiv X ((𝟙 X : X ⟶ X).baseHom) _).injective
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact (Category.assoc _ _ _).trans
      ((congrArg (X.pullbackAlongπ ((𝟙 X : X ⟶ X).baseHom) ≫ ·)
        (EllObj.toPullbackAlong_pullbackAlongπ (𝟙 X))).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm))
  · show 𝟙 X.base ≫ 𝟙 X.base = 𝟙 X.base
    rw [Category.comp_id]

/-- **The projection is surjective on geometric points** ([GHB7-geom-s], KM 7.1.3(3)
surjectivity half): over an algebraically closed field every section of the chosen
quotient lifts to a value of `Q`, because the base change of the finite étale
surjective `π` along the section has a section (`natCard_sections_eq_finrank` +
`one_le_finrank_iff_surjective`). -/
theorem QuotPkg.projQ_geom_surjective (pkg : ∀ X : EllObj R, QuotPkg φ X)
    (hfree : FreeAction φ)
    (k : Type u) [Field k] [IsAlgClosed k]
    (sm : Spec (CommRingCat.of k) ⟶ Spec R)
    (E : EllipticCurve (Spec (CommRingCat.of k))) :
    Function.Surjective
      ((QuotPkg.projQ pkg hfree).app
        (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R))) := by
  set X : EllObj R := ⟨Spec (CommRingCat.of k), sm, E⟩ with hXdef
  intro s
  obtain ⟨hfin, het, hsurj⟩ := (pkg X).π_finite_etale_surjective hfree
  haveI := hfin; haveI := het; haveI := hsurj
  haveI : IsFinite (pullback.snd (pkg X).π s.1) :=
    MorphismProperty.pullback_snd _ _ hfin
  haveI : Etale (pullback.snd (pkg X).π s.1) :=
    MorphismProperty.pullback_snd _ _ het
  -- a section of the base-changed projection exists
  have hne : Nonempty ↑(Spec (CommRingCat.of k)) := by
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨x₀⟩ := hne
  have hcard := natCard_sections_eq_finrank (k := k)
    (pullback.snd (pkg X).π s.1) x₀
  have hpos : 1 ≤ (pullback.snd (pkg X).π s.1).finrank x₀ := by
    rw [Scheme.Hom.finrank_pullback_snd]
    exact (Scheme.Hom.one_le_finrank_iff_surjective (pkg X).π).mpr hsurj _
  obtain ⟨⟨t, ht⟩⟩ := Nat.card_pos_iff.mp (hcard ▸ hpos) |>.1
  -- the lifted classifying section and its value
  have hmem : (t ≫ pullback.fst (pkg X).π s.1) ≫ (pkg X).d.f =
      (𝟙 X : X ⟶ X).baseHom := by
    rw [show (pkg X).d.f = (pkg X).π ≫ (pkg X).f₀ from (pkg X).hπf.symm]
    exact (Category.assoc _ _ _).trans
      ((congrArg (t ≫ ·) ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (pkg X).f₀) pullback.condition).trans
          ((Category.assoc _ _ _).trans
            (congrArg (pullback.snd (pkg X).π s.1 ≫ ·) s.2))))).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ 𝟙 X.base) ht).trans
            ((Category.id_comp _).trans rfl))))
  refine ⟨Q.map (EllObj.toPullbackAlong (𝟙 X)).op
    ((pkg X).d.eqv ((𝟙 X : X ⟶ X).baseHom)
      ⟨t ≫ pullback.fst (pkg X).π s.1, hmem⟩), ?_⟩
  refine Subtype.ext ?_
  have hcollapse : Q.map (X.pullbackAlongπ ((𝟙 X : X ⟶ X).baseHom)).op
      (Q.map (EllObj.toPullbackAlong (𝟙 X)).op
        ((pkg X).d.eqv ((𝟙 X : X ⟶ X).baseHom)
          ⟨t ≫ pullback.fst (pkg X).π s.1, hmem⟩)) =
      (pkg X).d.eqv ((𝟙 X : X ⟶ X).baseHom)
        ⟨t ≫ pullback.fst (pkg X).π s.1, hmem⟩ :=
    (FunctorToTypes.map_comp_apply Q (EllObj.toPullbackAlong (𝟙 X)).op
      (X.pullbackAlongπ ((𝟙 X : X ⟶ X).baseHom)).op _).symm.trans
      ((congrArg (fun m => Q.map m ((pkg X).d.eqv ((𝟙 X : X ⟶ X).baseHom)
        ⟨t ≫ pullback.fst (pkg X).π s.1, hmem⟩))
        (show (EllObj.toPullbackAlong (𝟙 X)).op ≫
            (X.pullbackAlongπ ((𝟙 X : X ⟶ X).baseHom)).op =
            𝟙 (Opposite.op (X.pullbackAlong ((𝟙 X : X ⟶ X).baseHom))) from
          congrArg Quiver.Hom.op
            (ModularCurves.EllObj.pullbackAlongπ_toPullbackAlong_id X))).trans
        (FunctorToTypes.map_id_apply Q _))
  show (((pkg X).d.eqv ((𝟙 X : X ⟶ X).baseHom)).symm
      (Q.map (X.pullbackAlongπ ((𝟙 X : X ⟶ X).baseHom)).op
        (Q.map (EllObj.toPullbackAlong (𝟙 X)).op
          ((pkg X).d.eqv ((𝟙 X : X ⟶ X).baseHom)
            ⟨t ≫ pullback.fst (pkg X).π s.1, hmem⟩)))).1 ≫ (pkg X).π = s.1
  rw [hcollapse, Equiv.symm_apply_apply]
  exact (Category.assoc _ _ _).trans
    ((congrArg (t ≫ ·) pullback.condition).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ s.1) ht).trans (Category.id_comp s.1))))

open Pointwise in
/-- **The `k̄`-point orbit lemma** ([GHB7-geom-o] chart level): over an algebraically
closed field, two algebra homomorphisms to the base field agreeing on the invariants
differ by the group action (`exists_smul_of_under_eq` + equal-kernel rigidity of
points valued in the base field). -/
theorem _root_.AlgebraicGeometry.exists_smul_algHom_eq
    {k B : Type u} [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B]
    {G : Type u_1} [Group G] [Finite G] [MulSemiringAction G B]
    [SMulCommClass G k B] (a₁ a₂ : B →ₐ[k] k)
    (hagree : ∀ b : B, (∀ g : G, g • b = b) → a₁ b = a₂ b) :
    ∃ g : G, ∀ b : B, a₂ b = a₁ (g • b) := by
  classical
  haveI : Algebra.IsInvariant (FixedPoints.subalgebra k B G) B G :=
    ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  haveI h₁ : (RingHom.ker a₁.toRingHom).IsPrime := RingHom.ker_isPrime _
  haveI h₂ : (RingHom.ker a₂.toRingHom).IsPrime := RingHom.ker_isPrime _
  obtain ⟨g₀, hg₀⟩ := Algebra.IsInvariant.exists_smul_of_under_eq
    (FixedPoints.subalgebra k B G) B G
    (RingHom.ker a₁.toRingHom) (RingHom.ker a₂.toRingHom)
    (by
      ext b'
      show algebraMap _ B b' ∈ RingHom.ker a₁.toRingHom ↔
        algebraMap _ B b' ∈ RingHom.ker a₂.toRingHom
      rw [RingHom.mem_ker, RingHom.mem_ker]
      have hfix : ∀ g : G, g • (b' : B) = (b' : B) := b'.2
      rw [show a₁.toRingHom (algebraMap _ B b') = a₁ (b' : B) from rfl,
        show a₂.toRingHom (algebraMap _ B b') = a₂ (b' : B) from rfl,
        hagree (b' : B) hfix])
  refine ⟨g₀⁻¹, fun b => ?_⟩
  -- the twisted point has the same kernel as `a₂`, hence equals it
  have hker : ∀ x : B, a₂ x = 0 ↔ a₁ (g₀⁻¹ • x) = 0 := by
    intro x
    constructor
    · intro hx
      have : x ∈ g₀ • RingHom.ker a₁.toRingHom := hg₀ ▸ (RingHom.mem_ker.mpr hx)
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at this
      exact RingHom.mem_ker.mp this
    · intro hx
      have : x ∈ g₀ • RingHom.ker a₁.toRingHom := by
        rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
        exact RingHom.mem_ker.mpr hx
      rw [← hg₀] at this
      exact RingHom.mem_ker.mp this
  -- rigidity: agree via the common kernel and `k`-linearity
  have hsmul_alg : ∀ c : k, g₀⁻¹ • (algebraMap k B c) = algebraMap k B c := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one, smul_comm g₀⁻¹ c (1 : B), smul_one]
  have hz : a₂ (b - algebraMap k B (a₁ (g₀⁻¹ • b))) = 0 := by
    rw [(hker _)]
    rw [smul_sub, hsmul_alg, map_sub, AlgHom.commutes, sub_eq_zero]
    rfl
  rw [map_sub, AlgHom.commutes, sub_eq_zero] at hz
  exact hz

/-- **Sections over `k̄` in the same fibre of the chosen projection lie in one
orbit** ([GHB7-geom-o] scheme level): via the affine model, `Spec`-faithfulness, and
the `k̄`-point orbit lemma. -/
theorem QuotPkg.exists_smul_of_π_eq (pkg : ∀ X : EllObj R, QuotPkg φ X)
    (hfree : FreeAction φ)
    {X : EllObj R} (k : Type u) [Field k] [IsAlgClosed k]
    (hXb : X.base = Spec (CommRingCat.of k))
    (h₁ h₂ : X.base ⟶ (pkg X).d.Z)
    (hf₁ : h₁ ≫ (pkg X).d.f = 𝟙 X.base) (hf₂ : h₂ ≫ (pkg X).d.f = 𝟙 X.base)
    (hπeq : h₁ ≫ (pkg X).π = h₂ ≫ (pkg X).π) :
    ∃ γ : G, h₂ = h₁ ≫ (pkg X).d.σZ.hom γ := by
  haveI := (pkg X).d.finite
  haveI : IsAffineHom (pkg X).d.f := inferInstance
  haveI : IsAffine X.base := by rw [hXb]; infer_instance
  haveI : IsAffine (pkg X).d.Z := isAffine_of_isAffineHom (pkg X).d.f
  -- the global-sections action
  have htop : (pkg X).d.σZ.IsStableOpen ⊤ := fun γ => by
    show ((pkg X).d.σZ.hom γ) ⁻¹ᵁ ⊤ = ⊤
    simp
  letI := (pkg X).d.σZ.gammaMulSemiringAction htop
  -- the `k`-algebra structure through the structure map
  set ψ : CommRingCat.of k ⟶ Γ((pkg X).d.Z, ⊤) :=
    Spec.preimage ((pkg X).d.Z.isoSpec.inv ≫ (pkg X).d.f ≫
      (eqToHom hXb : X.base ⟶ Spec (CommRingCat.of k))) with hψdef
  have hψ : Spec.map ψ = (pkg X).d.Z.isoSpec.inv ≫ (pkg X).d.f ≫ eqToHom hXb :=
    Spec.map_preimage _
  letI : Algebra k ↑Γ((pkg X).d.Z, ⊤) := ψ.hom.toAlgebra
  have hAlg : algebraMap k ↑Γ((pkg X).d.Z, ⊤) = ψ.hom := rfl
  -- the action bridge: `Spec` of the smul ring hom is the conjugated action
  have hbridge : ∀ γ : G, (pkg X).d.Z.isoSpec.hom ≫
      AlgebraicGeometry.specSMul (G := G) (B := ↑Γ((pkg X).d.Z, ⊤)) γ =
      (pkg X).d.σZ.hom γ ≫ (pkg X).d.Z.isoSpec.hom := by
    intro γ
    have hofHom : CommRingCat.ofHom
        (MulSemiringAction.toRingHom G ↑Γ((pkg X).d.Z, ⊤) γ) =
        ((pkg X).d.σZ.hom γ).appTop := by
      ext b
      show (((pkg X).d.σZ.hom γ).appLE ⊤ ⊤ (htop γ).ge).hom b =
        (((pkg X).d.σZ.hom γ).appTop).hom b
      simp [Scheme.Hom.appLE]
    rw [AlgebraicGeometry.specSMul, hofHom]
    exact Scheme.isoSpec_hom_naturality ((pkg X).d.σZ.hom γ)
  -- the action fixes the `k`-structure
  have hψinv : ∀ (γ : G) (c : k), γ • (ψ.hom c) = ψ.hom c := by
    intro γ c
    have hofHom : CommRingCat.ofHom
        (MulSemiringAction.toRingHom G ↑Γ((pkg X).d.Z, ⊤) γ) =
        ((pkg X).d.σZ.hom γ).appTop := by
      ext b
      show (((pkg X).d.σZ.hom γ).appLE ⊤ ⊤ (htop γ).ge).hom b =
        (((pkg X).d.σZ.hom γ).appTop).hom b
      simp [Scheme.Hom.appLE]
    have hmapeq : Spec.map (ψ ≫ ((pkg X).d.σZ.hom γ).appTop) = Spec.map ψ := by
      rw [Spec.map_comp, hψ,
        show Spec.map ((pkg X).d.σZ.hom γ).appTop =
          (pkg X).d.Z.isoSpec.inv ≫ (pkg X).d.σZ.hom γ ≫
            (pkg X).d.Z.isoSpec.hom from by
          rw [← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [reassoc_of% ((pkg X).d.over_base γ)]
    have hcomp : ψ ≫ ((pkg X).d.σZ.hom γ).appTop = ψ := Spec.map_injective hmapeq
    have := congrArg (fun (m : CommRingCat.of k ⟶ Γ((pkg X).d.Z, ⊤)) => m.hom c) hcomp
    simpa [← hofHom] using this
  haveI : SMulCommClass G k ↑Γ((pkg X).d.Z, ⊤) := ⟨fun γ c s => by
    show γ • (c • s) = c • (γ • s)
    rw [Algebra.smul_def, Algebra.smul_def, hAlg, smul_mul', hψinv γ c]⟩
  -- the two sections as `k`-points of the coordinate ring
  set φ₁ : Γ((pkg X).d.Z, ⊤) ⟶ CommRingCat.of k :=
    Spec.preimage ((eqToHom hXb.symm : Spec (CommRingCat.of k) ⟶ X.base) ≫ h₁ ≫
      (pkg X).d.Z.isoSpec.hom) with hφ₁def
  set φ₂ : Γ((pkg X).d.Z, ⊤) ⟶ CommRingCat.of k :=
    Spec.preimage ((eqToHom hXb.symm : Spec (CommRingCat.of k) ⟶ X.base) ≫ h₂ ≫
      (pkg X).d.Z.isoSpec.hom) with hφ₂def
  have hφ₁ : Spec.map φ₁ = (eqToHom hXb.symm : Spec (CommRingCat.of k) ⟶ X.base) ≫
      h₁ ≫ (pkg X).d.Z.isoSpec.hom := Spec.map_preimage _
  have hφ₂ : Spec.map φ₂ = (eqToHom hXb.symm : Spec (CommRingCat.of k) ⟶ X.base) ≫
      h₂ ≫ (pkg X).d.Z.isoSpec.hom := Spec.map_preimage _
  -- `k`-linearity from the section property
  have hcommutes : ∀ (hh : X.base ⟶ (pkg X).d.Z)
      (hhf : hh ≫ (pkg X).d.f = 𝟙 X.base)
      (φ : Γ((pkg X).d.Z, ⊤) ⟶ CommRingCat.of k)
      (hφ : Spec.map φ = (eqToHom hXb.symm : Spec (CommRingCat.of k) ⟶ X.base) ≫
        hh ≫ (pkg X).d.Z.isoSpec.hom), ψ ≫ φ = 𝟙 (CommRingCat.of k) := by
    intro hh hhf φ hφ
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hψ, Spec.map_id]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [reassoc_of% hhf]
    simp [eqToHom_trans]
  have hc₁ := hcommutes h₁ hf₁ φ₁ hφ₁
  have hc₂ := hcommutes h₂ hf₂ φ₂ hφ₂
  -- invariance agreement through the descended invariants map
  have hFinv : ∀ γ : G, (pkg X).d.σZ.hom γ ≫ ((pkg X).d.Z.isoSpec.hom ≫
      AlgebraicGeometry.invariantsπ G ↑Γ((pkg X).d.Z, ⊤) ℤ) =
      (pkg X).d.Z.isoSpec.hom ≫
        AlgebraicGeometry.invariantsπ G ↑Γ((pkg X).d.Z, ⊤) ℤ := by
    intro γ
    rw [← Category.assoc, ← hbridge γ, Category.assoc,
      AlgebraicGeometry.specSMul_invariantsπ]
  obtain ⟨w, hw, -⟩ := (pkg X).hdesc ((pkg X).d.Z.isoSpec.hom ≫
    AlgebraicGeometry.invariantsπ G ↑Γ((pkg X).d.Z, ⊤) ℤ) hFinv
  have hFeq : h₁ ≫ ((pkg X).d.Z.isoSpec.hom ≫
      AlgebraicGeometry.invariantsπ G ↑Γ((pkg X).d.Z, ⊤) ℤ) =
      h₂ ≫ ((pkg X).d.Z.isoSpec.hom ≫
        AlgebraicGeometry.invariantsπ G ↑Γ((pkg X).d.Z, ⊤) ℤ) := by
    rw [← hw, ← Category.assoc, hπeq, Category.assoc]
  -- assemble the algebra points and apply the orbit lemma
  obtain ⟨γ₀, hγ₀⟩ := AlgebraicGeometry.exists_smul_algHom_eq
    (k := k) (B := ↑Γ((pkg X).d.Z, ⊤)) (G := G)
    ⟨φ₁.hom, fun c => congrArg
      (fun (m : CommRingCat.of k ⟶ CommRingCat.of k) => m.hom c) hc₁⟩
    ⟨φ₂.hom, fun c => congrArg
      (fun (m : CommRingCat.of k ⟶ CommRingCat.of k) => m.hom c) hc₂⟩
    (by
      intro b hbfix
      have hmem : b ∈ FixedPoints.subalgebra ℤ ↑Γ((pkg X).d.Z, ⊤) G := hbfix
      have hSpec : Spec.map (CommRingCat.ofHom
          (algebraMap (FixedPoints.subalgebra ℤ ↑Γ((pkg X).d.Z, ⊤) G)
            ↑Γ((pkg X).d.Z, ⊤)) ≫ φ₁) =
          Spec.map (CommRingCat.ofHom
            (algebraMap (FixedPoints.subalgebra ℤ ↑Γ((pkg X).d.Z, ⊤) G)
              ↑Γ((pkg X).d.Z, ⊤)) ≫ φ₂) := by
        rw [Spec.map_comp, Spec.map_comp, hφ₁, hφ₂]
        show _ ≫ AlgebraicGeometry.invariantsπ G ↑Γ((pkg X).d.Z, ⊤) ℤ =
          _ ≫ AlgebraicGeometry.invariantsπ G ↑Γ((pkg X).d.Z, ⊤) ℤ
        simp only [Category.assoc]
        exact congrArg ((eqToHom hXb.symm :
          Spec (CommRingCat.of k) ⟶ X.base) ≫ ·) hFeq
      have hh := Spec.map_injective hSpec
      exact congrArg (fun (m : CommRingCat.of
        (FixedPoints.subalgebra ℤ ↑Γ((pkg X).d.Z, ⊤) G) ⟶ CommRingCat.of k) =>
        m.hom ⟨b, hmem⟩) hh)
  -- translate the orbit back to the scheme side
  refine ⟨γ₀, ?_⟩
  have hφeq : φ₂ = CommRingCat.ofHom
      (MulSemiringAction.toRingHom G ↑Γ((pkg X).d.Z, ⊤) γ₀) ≫ φ₁ := by
    ext b
    exact hγ₀ b
  have hSpec2 : Spec.map φ₂ = Spec.map φ₁ ≫
      AlgebraicGeometry.specSMul (G := G) γ₀ := by
    rw [hφeq, Spec.map_comp]
    rfl
  rw [hφ₁, hφ₂] at hSpec2
  have hσ : (eqToHom hXb.symm : Spec (CommRingCat.of k) ⟶ X.base) ≫ h₂ ≫
      (pkg X).d.Z.isoSpec.hom =
      (eqToHom hXb.symm : Spec (CommRingCat.of k) ⟶ X.base) ≫
        (h₁ ≫ (pkg X).d.σZ.hom γ₀) ≫ (pkg X).d.Z.isoSpec.hom := by
    rw [hSpec2]
    simp only [Category.assoc]
    rw [← hbridge γ₀]
  have := (cancel_epi (eqToHom hXb.symm :
    Spec (CommRingCat.of k) ⟶ X.base)).mp hσ
  exact (cancel_mono (pkg X).d.Z.isoSpec.hom).mp this

/-- **The fibres of the projection over `k̄` are the `G`-orbits** ([GHB7-geom-o],
KM 7.1.3(3) injectivity half; Loeffler Fact 3.8.1's "H-orbits"). -/
theorem QuotPkg.projQ_geom_orbits (pkg : ∀ X : EllObj R, QuotPkg φ X)
    (hfree : FreeAction φ)
    (k : Type u) [Field k] [IsAlgClosed k]
    {X : EllObj R} (hXb : X.base = Spec (CommRingCat.of k))
    (a b : Q.obj (Opposite.op X)) :
    (QuotPkg.projQ pkg hfree).app (Opposite.op X) a =
      (QuotPkg.projQ pkg hfree).app (Opposite.op X) b ↔
    ∃ γ : G, (φ γ).hom.app (Opposite.op X) a = b := by
  constructor
  · intro heq
    -- the classifying sections lie in one fibre, hence one orbit
    have hval : (((pkg X).d.eqv ((𝟙 X : X ⟶ X).baseHom)).symm
        (Q.map (X.pullbackAlongπ ((𝟙 X : X ⟶ X).baseHom)).op a)).1 ≫
        (pkg X).π =
        (((pkg X).d.eqv ((𝟙 X : X ⟶ X).baseHom)).symm
        (Q.map (X.pullbackAlongπ ((𝟙 X : X ⟶ X).baseHom)).op b)).1 ≫
        (pkg X).π := congrArg Subtype.val heq
    obtain ⟨γ₀, hγ₀⟩ := QuotPkg.exists_smul_of_π_eq pkg hfree (X := X) k hXb
      ((((pkg X).d.eqv ((𝟙 X : X ⟶ X).baseHom)).symm
        (Q.map (X.pullbackAlongπ ((𝟙 X : X ⟶ X).baseHom)).op a)).1)
      ((((pkg X).d.eqv ((𝟙 X : X ⟶ X).baseHom)).symm
        (Q.map (X.pullbackAlongπ ((𝟙 X : X ⟶ X).baseHom)).op b)).1)
      ((((pkg X).d.eqv ((𝟙 X : X ⟶ X).baseHom)).symm
        (Q.map (X.pullbackAlongπ ((𝟙 X : X ⟶ X).baseHom)).op a)).2)
      ((((pkg X).d.eqv ((𝟙 X : X ⟶ X).baseHom)).symm
        (Q.map (X.pullbackAlongπ ((𝟙 X : X ⟶ X).baseHom)).op b)).2)
      hval
    refine ⟨γ₀⁻¹, ?_⟩
    -- transfer through the equivariance of the classifying bijection
    have hm : ((((pkg X).d.eqv ((𝟙 X : X ⟶ X).baseHom)).symm
        (Q.map (X.pullbackAlongπ ((𝟙 X : X ⟶ X).baseHom)).op a)).1 ≫
        (pkg X).d.σZ.hom γ₀) ≫ (pkg X).d.f = (𝟙 X : X ⟶ X).baseHom := by
      rw [Category.assoc, (pkg X).d.over_base γ₀]
      exact ((((pkg X).d.eqv ((𝟙 X : X ⟶ X).baseHom)).symm
        (Q.map (X.pullbackAlongπ ((𝟙 X : X ⟶ X).baseHom)).op a)).2)
    have hQside : Q.map (X.pullbackAlongπ ((𝟙 X : X ⟶ X).baseHom)).op b =
        Q.map (X.pullbackAlongπ ((𝟙 X : X ⟶ X).baseHom)).op
          ((φ γ₀⁻¹).hom.app (Opposite.op X) a) := by
      calc Q.map (X.pullbackAlongπ ((𝟙 X : X ⟶ X).baseHom)).op b
          = (pkg X).d.eqv ((𝟙 X : X ⟶ X).baseHom)
            (((pkg X).d.eqv ((𝟙 X : X ⟶ X).baseHom)).symm
              (Q.map (X.pullbackAlongπ ((𝟙 X : X ⟶ X).baseHom)).op b)) :=
            (((pkg X).d.eqv ((𝟙 X : X ⟶ X).baseHom)).apply_symm_apply _).symm
        _ = (pkg X).d.eqv ((𝟙 X : X ⟶ X).baseHom)
            ⟨(((pkg X).d.eqv ((𝟙 X : X ⟶ X).baseHom)).symm
              (Q.map (X.pullbackAlongπ ((𝟙 X : X ⟶ X).baseHom)).op a)).1 ≫
              (pkg X).d.σZ.hom γ₀, hm⟩ :=
            congrArg _ (Subtype.ext hγ₀)
        _ = (φ γ₀⁻¹).hom.app (Opposite.op (X.pullbackAlong
              ((𝟙 X : X ⟶ X).baseHom)))
            ((pkg X).d.eqv ((𝟙 X : X ⟶ X).baseHom)
              (((pkg X).d.eqv ((𝟙 X : X ⟶ X).baseHom)).symm
                (Q.map (X.pullbackAlongπ ((𝟙 X : X ⟶ X).baseHom)).op a))) :=
            (pkg X).d.equivariant ((𝟙 X : X ⟶ X).baseHom)
              (((pkg X).d.eqv ((𝟙 X : X ⟶ X).baseHom)).symm
                (Q.map (X.pullbackAlongπ ((𝟙 X : X ⟶ X).baseHom)).op a)) γ₀
        _ = (φ γ₀⁻¹).hom.app (Opposite.op (X.pullbackAlong
              ((𝟙 X : X ⟶ X).baseHom)))
            (Q.map (X.pullbackAlongπ ((𝟙 X : X ⟶ X).baseHom)).op a) :=
            congrArg _ (((pkg X).d.eqv
              ((𝟙 X : X ⟶ X).baseHom)).apply_symm_apply _)
        _ = Q.map (X.pullbackAlongπ ((𝟙 X : X ⟶ X).baseHom)).op
            ((φ γ₀⁻¹).hom.app (Opposite.op X) a) :=
            NatTrans.naturality_apply (φ γ₀⁻¹).hom
              (X.pullbackAlongπ ((𝟙 X : X ⟶ X).baseHom)).op a
    -- recover the values through the tautological roundtrip
    have hrec : ∀ y : Q.obj (Opposite.op X),
        Q.map (EllObj.toPullbackAlong (𝟙 X)).op
          (Q.map (X.pullbackAlongπ ((𝟙 X : X ⟶ X).baseHom)).op y) = y := by
      intro y
      exact (FunctorToTypes.map_comp_apply Q
        (X.pullbackAlongπ ((𝟙 X : X ⟶ X).baseHom)).op
        (EllObj.toPullbackAlong (𝟙 X)).op y).symm.trans
        ((congrArg (fun m => Q.map m y)
          (show (X.pullbackAlongπ ((𝟙 X : X ⟶ X).baseHom)).op ≫
              (EllObj.toPullbackAlong (𝟙 X)).op = 𝟙 (Opposite.op X) from
            congrArg Quiver.Hom.op
              (EllObj.toPullbackAlong_pullbackAlongπ (𝟙 X)))).trans
          (FunctorToTypes.map_id_apply Q y))
    have := congrArg (Q.map (EllObj.toPullbackAlong (𝟙 X)).op) hQside
    rw [hrec b, hrec ((φ γ₀⁻¹).hom.app (Opposite.op X) a)] at this
    exact this.symm
  · rintro ⟨γ, rfl⟩
    exact (congrArg (fun η : Q ⟶ QuotPkg.quotProb pkg hfree =>
      η.app (Opposite.op X) a)
      (QuotPkg.projQ_invariant pkg hfree γ)).symm

end Transport









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
  let pkg : ∀ X : EllObj R, QuotPkg φ X := fun X =>
    (nonempty_quotPkg φ hdata X).some
  refine ⟨⟨QuotPkg.quotProb pkg hfree, QuotPkg.projQ pkg hfree,
    QuotPkg.projQ_invariant pkg hfree,
    QuotPkg.relRep_quotProb pkg hfree, ?_, ?_, ?_⟩⟩
  · -- couniversal (KM 7.1.3(1) verbatim)
    intro P' hP' ν' hν'
    let dP : ∀ X : EllObj R, ModuliProblem.RelRepData P' X := fun X =>
      ((ModuliProblem.relativelyRepresentable_iff_nonempty_relRepData P').mp
        hP' X).some
    have hct := fun X : EllObj R =>
      QuotPkg.exists_crossTransport (pkg X) (dP X) ν' hν'
    let νf : ∀ X : EllObj R, (pkg X).d.Z ⟶ (dP X).Z := fun X => (hct X).choose
    have hνf : ∀ X : EllObj R, νf X ≫ (dP X).f = (pkg X).d.f := fun X =>
      (hct X).choose_spec.choose
    have hcl : ∀ X : EllObj R, (dP X).eqv (pkg X).d.f ⟨νf X, hνf X⟩ =
        ν'.app (Opposite.op (X.pullbackAlong (pkg X).d.f))
          ((pkg X).d.eqv (pkg X).d.f
            ⟨𝟙 (pkg X).d.Z, Category.id_comp (pkg X).d.f⟩) := fun X =>
      (hct X).choose_spec.choose_spec.1
    have hνinv : ∀ (X : EllObj R) (γ : G),
        (pkg X).d.σZ.hom γ ≫ νf X = νf X := fun X =>
      (hct X).choose_spec.choose_spec.2
    have hcd := fun X : EllObj R =>
      QuotPkg.exists_crossDescent (pkg X) (dP X) (νf X) (hνf X) (hνinv X)
    let μf : ∀ X : EllObj R, (pkg X).Z₀ ⟶ (dP X).Z := fun X => (hcd X).choose
    have hμ : ∀ X : EllObj R, (pkg X).π ≫ μf X = νf X := fun X =>
      (hcd X).choose_spec.1
    have hμf : ∀ X : EllObj R, μf X ≫ (dP X).f = (pkg X).f₀ := fun X =>
      (hcd X).choose_spec.2.1
    exact ⟨QuotPkg.crossμ pkg hfree dP ν' νf hνf hcl μf hμ hμf,
      QuotPkg.projQ_crossμ pkg hfree dP ν' νf hνf hcl μf hμ hμf,
      fun μ'' hμ'' => QuotPkg.crossμ_unique pkg hfree dP ν' νf hνf hcl
        hνinv μf hμ hμf μ'' hμ''⟩
  · -- geometric surjectivity (KM 7.1.3(3), surjectivity half)
    intro k _ _ sm E
    exact QuotPkg.projQ_geom_surjective pkg hfree k sm E
  · -- fibres are orbits (KM 7.1.3(3), injectivity half)
    intro k _ _ sm E a b
    exact QuotPkg.projQ_geom_orbits pkg hfree k rfl a b

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

/-- The `glSmul g`-translation of the naive full-level problem, as an endomorphism of
the moduli functor: componentwise `glSmul g`, natural by `pullSection_glSmul`
(KM's diagram 7.1.1.1, de-sorried with T-E4a). -/
noncomputable def glSmulNat (N : ℕ) [NeZero N]
    (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    gammaFullNaiveProblem R N ⟶ gammaFullNaiveProblem R N where
  app X := ↾fun L => X.unop.curve.glSmul g L
  naturality X Y f := by
    ext L
    show Y.unop.curve.glSmul g ((gammaFullNaiveProblem R N).map f L)
        = (gammaFullNaiveProblem R N).map f (X.unop.curve.glSmul g L)
    exact EllHom.pullSection_glSmul R f.unop g L

@[simp]
theorem glSmulNat_app (N : ℕ) [NeZero N]
    (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) (X : (EllObj R)ᵒᵖ)
    (L : (gammaFullNaiveProblem R N).obj X) :
    (glSmulNat R N g).app X L = X.unop.curve.glSmul g L := rfl

/-- **[GH1, de-sorried 2026-07-15] (Loeffler Fact 3.8.1; KM 7.1.1)** The `H`-action on
the naive full-level problem: `γ` acts on values by `glSmul (γ⁻¹)` (the inverse
because `glSmul_mul` is a RIGHT action law — the 2026-07-06 adversarial fix in
`Moduli/GammaH.lean` — while `Aut`-valued homomorphisms are left actions). Naturality
of the components is KM's diagram 7.1.1.1 = `pullSection_glSmul`, unlocked by T-E4a
(`EllHom.pullSection_add`, de-sorried by STREAM-OMEGA). Consumers use only this def
and its spec `gammaHAut_app_val`. -/
noncomputable def gammaHAut (N : ℕ) [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N))) :
    ↥H →* Aut (gammaFullNaiveProblem R N) where
  toFun γ :=
    { hom := glSmulNat R N ((γ⁻¹ : ↥H) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
      inv := glSmulNat R N ((γ : ↥H) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
      hom_inv_id := by
        ext X L
        show ((glSmulNat R N ((γ⁻¹ : ↥H) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))).app X ≫
            (glSmulNat R N ((γ : ↥H) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))).app X) L
          = (𝟙 ((gammaFullNaiveProblem R N).obj X)) L
        rw [CategoryTheory.comp_apply, CategoryTheory.id_apply, glSmulNat_app, glSmulNat_app,
          ← EllipticCurve.glSmul_mul]
        have hcoe : (((γ⁻¹ : ↥H) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))) *
            ((γ : ↥H) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) = 1 := by
          rw [show (((γ⁻¹ : ↥H)) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
              = ((γ : ↥H) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))⁻¹ from rfl,
            inv_mul_cancel]
        rw [hcoe, EllipticCurve.glSmul_one]
      inv_hom_id := by
        ext X L
        show ((glSmulNat R N ((γ : ↥H) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))).app X ≫
            (glSmulNat R N ((γ⁻¹ : ↥H) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))).app X) L
          = (𝟙 ((gammaFullNaiveProblem R N).obj X)) L
        rw [CategoryTheory.comp_apply, CategoryTheory.id_apply, glSmulNat_app, glSmulNat_app,
          ← EllipticCurve.glSmul_mul]
        have hcoe : ((γ : ↥H) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) *
            (((γ⁻¹ : ↥H) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))) = 1 := by
          rw [show (((γ⁻¹ : ↥H)) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
              = ((γ : ↥H) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))⁻¹ from rfl,
            mul_inv_cancel]
        rw [hcoe, EllipticCurve.glSmul_one] }
  map_one' := by
    ext X L
    show X.unop.curve.glSmul
      (((1 : ↥H)⁻¹ : ↥H) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) L = L
    rw [show ((((1 : ↥H)⁻¹ : ↥H)) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
        = 1 by rw [inv_one]; rfl]
    rw [EllipticCurve.glSmul_one]
  map_mul' γ δ := by
    ext X L
    show (glSmulNat R N ((((γ * δ)⁻¹ : ↥H)) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))).app
        X L
      = ((glSmulNat R N (((δ⁻¹ : ↥H)) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))).app X ≫
        (glSmulNat R N (((γ⁻¹ : ↥H)) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))).app X) L
    rw [CategoryTheory.comp_apply, glSmulNat_app, glSmulNat_app, glSmulNat_app]
    rw [show ((((γ * δ)⁻¹ : ↥H)) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
        = (((δ⁻¹ : ↥H)) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) *
          (((γ⁻¹ : ↥H)) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) by
      rw [mul_inv_rev]; rfl]
    rw [EllipticCurve.glSmul_mul]

/-- **[GH1, specification]** The value pin of `gammaHAut`: `γ` acts by
`glSmul (γ⁻¹ : GL₂(ℤ/N))`. (Both this and the def discharge together; the pin is what
[GHC3]'s `Quotient.lift` and [GH2]'s freeness argument consume.) -/
theorem gammaHAut_app_val (N : ℕ) [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N))) (γ : ↥H)
    (X : EllObj R) (L : (gammaFullNaiveProblem R N).obj (Opposite.op X)) :
    (gammaHAut R N H γ).hom.app (Opposite.op X) L =
      X.curve.glSmul ((γ⁻¹ : ↥H) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) L :=
  rfl

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
    Etale (levelSpaceΓπ E N) :=
  levelSpaceΓ_structure_etale E N h

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
  obtain ⟨d, hfin, het⟩ := gammaFullNaive_relRepData R N hinv X
  exact ModuliProblem.RelRepData.exists_equivariant (gammaHAut R N H) d hfin het

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
    Nonempty (ModuliProblem.QuotientProblemData (gammaHAut R N H)) :=
  -- [GHB7] applied to the `H`-action: freeness = [GH2] (`gammaFullNaive_freeAction`),
  -- equivariant finite-étale data at every object = [GHA5]
  -- (`gammaFullNaive_equivariantRelRepData`). `Finite ↥H` is inferred from the finiteness
  -- of `GL₂(ℤ/N)` (`N` invertible ⟹ `NeZero N` ⟹ `ZMod N` finite).
  ModuliProblem.exists_quotientProblemData (gammaHAut R N H)
    (gammaFullNaive_freeAction R N H hinv)
    (fun X => gammaFullNaive_equivariantRelRepData R N H hinv X)

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
  -- Well-definedness of `Quotient.lift pkg.proj.app`: the projection is constant on
  -- `H`-orbits (`proj_invariant` at `⟨g,hg⟩⁻¹` + the `gammaHAut_app_val` pin absorb the
  -- `γ⁻¹` twist — `H` a group makes `g ↦ g⁻¹` a bijection of `H`).
  have wd : ∀ (X : EllObj R) (a b : X.curve.FullLevelPt N),
      (X.curve.hOrbitSetoid H) a b →
      pkg.proj.app (Opposite.op X) a = pkg.proj.app (Opposite.op X) b := by
    rintro X a b ⟨g, hg, rfl⟩
    have h := ConcreteCategory.congr_hom
      (NatTrans.congr_app (pkg.proj_invariant ((⟨g, hg⟩ : ↥H)⁻¹)) (Opposite.op X)) a
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, gammaHAut_app_val, inv_inv] at h
    exact h.symm
  -- The comparison natural transformation `θ.app X = Quotient.lift pkg.proj.app`.
  refine ⟨{ app := fun X => ↾Quotient.lift (fun L => pkg.proj.app X L) (wd X.unop)
            naturality := ?_ }, ?_, ?_⟩
  · -- naturality: check on `Quotient.mk L`. The orbit-map step `e1` closes by proof
    -- irrelevance on the `FullLevelPt` subtype (the `.val`s are the *same* `pullSection`
    -- term), so `pullSection` is never unfolded; the `θ`/`proj` step is the cheap
    -- `Quotient.lift_mk` reduction — together reducing to `pkg.proj`'s naturality.
    intro X Y f
    ext q
    induction q using Quotient.ind with
    | _ L =>
      have e1 : (gammaHNaiveProblem R N H).map f
            (Quotient.mk ((Opposite.unop X).curve.hOrbitSetoid H) L)
          = Quotient.mk ((Opposite.unop Y).curve.hOrbitSetoid H)
            ((gammaFullNaiveProblem R N).map f L) := rfl
      simp only [TypeCat.Fun.toFun_apply, types_comp_apply,
        TypeCat.hom_ofHom, TypeCat.Fun.mk_apply, e1, Quotient.lift_mk]
      have hn := ConcreteCategory.congr_hom (pkg.proj.naturality f) L
      simpa only [types_comp_apply] using hn
  · -- clause 1: `θ ∘ mk = pkg.proj` by `Quotient.lift_mk`.
    intro X L; rfl
  · -- geometric bijectivity from `geom_surjective` + `geom_orbits`.
    intro k _ _ sm E
    set W : EllObj R := ⟨Spec (CommRingCat.of k), sm, E⟩ with hW
    constructor
    · -- injective: equal projections ⟹ same `H`-orbit (`geom_orbits` + the pin).
      intro q₁ q₂ hq
      induction q₁ using Quotient.ind with
      | _ L₁ =>
      induction q₂ using Quotient.ind with
      | _ L₂ =>
        have hproj : pkg.proj.app (Opposite.op W) L₁ = pkg.proj.app (Opposite.op W) L₂ := hq
        obtain ⟨γ, hγ⟩ := (pkg.geom_orbits k sm E L₁ L₂).mp hproj
        rw [gammaHAut_app_val] at hγ
        exact Quotient.sound ⟨((γ⁻¹ : ↥H) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)),
          (γ⁻¹ : ↥H).2, hγ⟩
    · -- surjective: `geom_surjective` + `mk` is surjective.
      intro y
      obtain ⟨L, hL⟩ := pkg.geom_surjective k sm E y
      exact ⟨Quotient.mk _ L, hL⟩

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

-- (`EllHom.pullSection_zsmul` now lives upstream in `Moduli/GammaH.lean`, T-H3a —
-- the identical local copy was deduplicated when T-E4a landed; STREAM-OMEGA 2026-07-14.)

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

-- (`asSection_injective` now comes through the `LevelSpaceEtaleClose` import chain
-- from `DrinfeldRepresentability`; the local copy was removed on the [GHA3] closing wire.)

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
  intro X
  obtain ⟨d, hfin, het⟩ := pkg.relRep X
  exact ⟨d.Z, d.f, hfin.toIsAffineHom, @d.eqv, @d.nat⟩

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
  have haff := pkg.affineOverEll
  exact (ModuliProblem.representable_iff pkg.prob haff).mpr ⟨haff.relativelyRepresentable, hrig⟩

end PartC

end ModularCurves
