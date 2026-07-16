/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.LevelStructure.ExactOrder
import ModularCurves.EllipticCurve.TorsionFibre
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# Finite locally free closed subgroup schemes of an elliptic curve (T-SG1)

The object KM's Γ₀(N) moduli problem quantifies over (KM 3.4 via KM 1.4.1, verbatim,
quote in hand): *"a closed subgroup-scheme `G ⊆ C` which is finite locally-free of rank
`N` over `S` is cyclic if, locally f.p.p.f. (SGA III, Exp. IV, 6.3) on `S`, `G` admits a
generator"*. This file defines the noun of that sentence — `FiniteLocallyFreeSubgroup E`:
a closed subscheme `G ↪ E`, finite locally free over the base, whose functor of points is
a subgroup functor in exactly the sense of KM 1.3.6 (verbatim: a divisor *"is a subgroup
of `C/S` if for every `S`-scheme `T` the subset `D(T)` of the group `C(T)` is in fact a
sub-group"*). Stream SG2 defines KM's fppf-local cyclicity against this layer (replacing
the `IsGammaZero` geometric-fibre surrogate, per the board GATE on Γ₀ representability);
SG3 states closedness of the cyclicity condition.

## Design decisions

* **Structure, not predicate.** A Γ₀(N)-structure *is* a choice of subgroup scheme — the
  subgroup is the datum of the moduli problem (KM 3.4) — so this layer must be a `Type`,
  not a `Prop` on pairs `(G, ι)`. This matches the project precedent:
  `RelEffCartierDiv` bundles the geometric datum as a structure, with the KM 1.3.6
  condition (`RelEffCartierDiv.IsSubgroup`) as a `Prop` on top. Here the subgroup
  condition is a *field*, so every inhabitant is honestly a subgroup scheme and SG2 can
  quantify over the type with no hypothesis plumbing (a bare `(G, ι)` record plus an
  `IsSubgroupScheme` predicate would reintroduce that plumbing everywhere and admit
  spurious inhabitants).

* **Scheme-plus-immersion data, not an ideal sheaf.** The D-lane encodes closed
  subschemes as `Scheme.IdealSheafData`; but the leading example `E[N] = E.torsion N` is
  born as a *pullback scheme with a morphism* (`torsionι`). Keeping `(G, ι)` as the data
  lets `torsionSubgroup` be `E.torsion N` on the nose, with no `ker`/`subscheme`
  transport in the definition. The two encodings interconvert: `toRelEffCartierDiv`
  (ideal := `ι.ker`, properties transported along the iso `ι.toImage`) and
  `ofRelEffCartierDiv` (for which the KM 1.3.6 predicate is *definitionally* the
  `subgroup` field — see its `subgroup := hD`); `toRelEffCartierDiv_ofRelEffCartierDiv`
  pins the retraction. Structure equality is intentionally NOT provided by an `ext`
  lemma: two subgroup schemes with distinct (but isomorphic) total spaces are distinct
  terms; identification happens through the divisor bridge (which is `ext`-able) or up
  to isomorphism in the moduli problems.

* **The subgroup condition mirrors `RelEffCartierDiv.IsSubgroup` verbatim**: for every
  `g : T ⟶ S` there is an `AddSubgroup` of `E.Point g` whose membership is "factors
  through `ι`". "Factors through" needs no uniqueness clause: `ι` is a closed immersion,
  hence a monomorphism, so lifts are unique. The `∃ H : AddSubgroup _` form silently
  encodes nonemptiness of `G(T)` for every `T` with a point (every subgroup contains
  `0`), so the empty subscheme over a nonempty base is *rightly* excluded, and the zero
  section always factors through every subgroup.

* **Rank is a predicate (`HasRank`), not a field.** The rank of a finite locally free
  morphism is locally constant, not constant — over a disconnected base honest subgroup
  schemes have jumping rank, so a rank field would wrongly shrink the type — and for
  `E[N]` the rank is a *theorem* (`torsion_rank`, KM 2.3.1), not data. The
  `∀ s, rank s = r` shape matches the existing conventions
  (`hdeg : ∀ s, D.degree s = N` in `RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors`
  and `IsGammaZero.degree_eq`), so SG2's "rank `N` and cyclic" hypotheses compose with
  the D-lane without adapters. The pointwise `rank` is also provided, as the `finrank`
  of the structure morphism (the spelling of `RelEffCartierDiv.degree` and
  `torsion_rank`).

## Sorries and their owners

* `HasRank.smul_eq_zero_of_factors` (KM 1.4.2: rank `N` ⟹ killed by `N`) is **derived**
  here from the already-registered box
  `RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors` (ExactOrder.lean, BB-DELIGNE /
  Oort–Tate, stream OT, ticket T-OT0) — no new box is minted for the Deligne argument.
* `baseChange.subgroup` and `pointSubgroup_baseChange` — T-SG1 follow-on (T-SG1b): the
  point-level base-change dictionary; this is the same
  `(E.baseChange g).E`-vs-`pullback E.π g` spelling normalisation that parks
  `Point.asSection_zsmul` (see the PARKED note in GroupLaw.lean).
* `torsionSubgroup` introduces **no new sorries**: the closed immersion is T-B3
  (`torsionι_isClosedImmersion`, proved), finiteness/flatness/rank are T-B4 (proved in
  Torsion.lean modulo the registered boxes BB-QF/BB-FLAT/BB-DEG), local finite
  presentation is `MulByHom.locallyOfFinitePresentation` (proved), and the subgroup
  condition is proved outright below (`torsionι_factors_iff`, from the kernel universal
  property `pointToTorsion` + `smul_eq_zero_iff_comp_mulByHom`).
-/

open AlgebraicGeometry CategoryTheory Limits

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}}

-- ATTACK (structure): (1) empty total space: `∅ ↪ E` is a closed immersion, finite flat
-- lfp over `S`, but the `subgroup` field kills it over any base with a point — every
-- `AddSubgroup` contains `0`, so the zero point of `E.Point g` must factor, and nothing
-- factors through `∅`; over `S = ∅` it survives, correctly (the trivial subgroup of the
-- empty curve). (2) uniqueness of the factoring lift: not required in the ∃ — `ι` is a
-- closed immersion hence a mono, so the lift is automatically unique; the set
-- `{P | ∃ h, h ≫ ι = P.1}` is honestly `G(T) ⊆ E(T)`. (3) non-reduced bases: the
-- condition quantifies over ALL `g : T ⟶ S` (Drinfeld register), not geometric points —
-- the `ℚ̄[ε]` counterexample recorded at `IsNaiveGammaOne` shows fibrewise surrogates
-- are strictly weaker. (4) group *scheme* structure: a multiplication morphism
-- `G ×_S G ⟶ G` is not a field; it is recoverable from the functorial condition applied
-- at the universal point `T := G ×_S G` (closed immersions are monos, so the factoring
-- of `m_E ∘ (ι × ι)` is unique and functorial) — deliberately deferred API, not data.
-- (5) rank ∉ fields: see the module docstring (jumping rank over disconnected bases).
/-- **A finite locally free closed subgroup scheme `G ⊆ E`** (KM 1.4.1's noun: *"a
closed subgroup-scheme `G ⊆ C` which is finite locally-free … over `S`"*; KM 1.3.6 for
the subgroup condition): a scheme `G` with a closed immersion `ι` into `E`, finite
locally free over the base (finite + flat + locally of finite presentation, the
`RelEffCartierDiv` spelling), such that for every `T ⟶ S` the `T`-points of `E` factoring
through `ι` form a subgroup of `E.Point g`.

The Γ₀(N)-moduli datum of stream SG (T-SG1); cyclicity of rank-`N` subgroups is T-SG2. -/
structure FiniteLocallyFreeSubgroup (E : EllipticCurve S) where
  /-- The total space of the subgroup scheme. -/
  G : Scheme.{u}
  /-- The inclusion of the subgroup into `E`. -/
  ι : G ⟶ E.E
  /-- `G ↪ E` is a closed subscheme (KM 1.4.1: "closed subgroup-scheme"). For the
  torsion example this is T-B3, `torsionι_isClosedImmersion` (proved). -/
  closedImmersion : IsClosedImmersion ι
  /-- `G` is finite over `S`. Together with `flat` and `lfp` this is "finite
  locally-free" (KM 1.4.1) in the project's `RelEffCartierDiv` spelling. For the
  torsion example this is T-B4, `torsionπ_isFinite` (proved modulo box BB-QF). -/
  finite : IsFinite (ι ≫ E.π)
  /-- `G` is flat over `S` (T-B4 / box BB-FLAT for the torsion example). -/
  flat : Flat (ι ≫ E.π)
  /-- `G` is locally of finite presentation over `S`. -/
  lfp : LocallyOfFinitePresentation (ι ≫ E.π)
  /-- **KM 1.3.6 subgroup condition** in functor-of-points form, mirroring
  `RelEffCartierDiv.IsSubgroup` verbatim: for every `g : T ⟶ S` the subset of
  `E.Point g` consisting of points factoring through `ι` is a subgroup — it contains
  `0` and is stable under addition and negation. -/
  subgroup : ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ S),
    ∃ H : AddSubgroup (E.Point g),
      ∀ P : E.Point g, P ∈ H ↔ ∃ h : T ⟶ G, h ≫ ι = P.1

attribute [instance] FiniteLocallyFreeSubgroup.closedImmersion
  FiniteLocallyFreeSubgroup.finite FiniteLocallyFreeSubgroup.flat
  FiniteLocallyFreeSubgroup.lfp

namespace FiniteLocallyFreeSubgroup

variable {E : EllipticCurve S}

/-- The structure morphism `G ⟶ S` of the subgroup scheme: the inclusion followed by
the structure morphism of `E`. An `abbrev`, so the `finite`/`flat`/`lfp` instance
fields apply to goals in either spelling. -/
abbrev π (G : FiniteLocallyFreeSubgroup E) : G.G ⟶ S := G.ι ≫ E.π

/-- The definitional equation of the structure morphism (mirror of `torsionι_π`). -/
@[reassoc]
theorem ι_π (G : FiniteLocallyFreeSubgroup E) : G.ι ≫ E.π = G.π := rfl

-- ATTACK (pointSubgroup): (1) choice-freeness: the carrier is the honest factoring set,
-- NOT `(G.subgroup g).choose` — so membership is `Iff.rfl` and does not depend on a
-- choice of witness subgroup; the closure fields eliminate the ∃ inside `Prop`, where
-- `obtain` is allowed. (2) the subgroup produced by the `subgroup` field is unique
-- (`AddSubgroup`s with the same membership are equal), so this canonical construction
-- agrees with any witness.
/-- The subgroup `G(T) ⊆ E(T)` of `T`-points of `E` over `g` factoring through `ι` —
KM 1.3.6's "`D(T)` is in fact a sub-group", as an honest `AddSubgroup` of `E.Point g`.
The carrier is definitionally the factoring set (`mem_pointSubgroup : … ↔ … := Iff.rfl`);
`zero_mem`, `add_mem`, `neg_mem` come from the `AddSubgroup` API. -/
def pointSubgroup (G : FiniteLocallyFreeSubgroup E) {T : Scheme.{u}} (g : T ⟶ S) :
    AddSubgroup (E.Point g) where
  carrier := {P : E.Point g | ∃ h : T ⟶ G.G, h ≫ G.ι = P.1}
  zero_mem' := by
    obtain ⟨H, hH⟩ := G.subgroup g
    exact (hH 0).mp H.zero_mem
  add_mem' := by
    intro P Q hP hQ
    obtain ⟨H, hH⟩ := G.subgroup g
    exact (hH _).mp (H.add_mem ((hH P).mpr hP) ((hH Q).mpr hQ))
  neg_mem' := by
    intro P hP
    obtain ⟨H, hH⟩ := G.subgroup g
    exact (hH _).mp (H.neg_mem ((hH P).mpr hP))

/-- Membership in `G.pointSubgroup g` is factoring through `ι` (the `mem`-style
characterisation; definitional). -/
@[simp]
theorem mem_pointSubgroup {G : FiniteLocallyFreeSubgroup E} {T : Scheme.{u}}
    {g : T ⟶ S} {P : E.Point g} :
    P ∈ G.pointSubgroup g ↔ ∃ h : T ⟶ G.G, h ≫ G.ι = P.1 :=
  Iff.rfl

-- ATTACK (rank/HasRank): (1) `Scheme.Hom.finrank` is a total function (junk without
-- finiteness/flatness), but every `FiniteLocallyFreeSubgroup` carries `finite`+`flat`,
-- so `rank` is always honest. (2) over `S = ∅`, `HasRank r` holds vacuously for EVERY
-- `r` simultaneously — consistent with the existing `∀ s, degree s = N` convention
-- (ExactOrder/IsGammaZero); consumers (`smul_eq_zero_of_factors`) stay sound because
-- point groups over the empty base are trivial. (3) `HasRank` demands GLOBALLY constant
-- rank, which is what KM 1.4.1's "of rank N" means; locally constant statements use
-- the pointwise `rank` directly.
/-- The rank of the subgroup scheme at `s : S`: the `finrank` of the finite locally
free structure morphism (locally constant in `s`; the `RelEffCartierDiv.degree` /
`torsion_rank` spelling). -/
noncomputable def rank (G : FiniteLocallyFreeSubgroup E) (s : S) : ℕ :=
  G.π.finrank s

/-- `G/S` has (globally constant) rank `r` — KM 1.4.1's "finite locally-free of rank
`N` over `S`". A predicate, not a structure field: see the module docstring. -/
def HasRank (G : FiniteLocallyFreeSubgroup E) (r : ℕ) : Prop :=
  ∀ s : S, G.rank s = r

/-! ### The divisor dictionary

`FiniteLocallyFreeSubgroup` ↔ the D-lane's `RelEffCartierDiv` + `IsSubgroup`
(KM 1.3.6). This is the interface SG2 uses to say "the divisor `Σₐ [aP₀]` equals `G`"
and the route by which the Deligne/Oort–Tate box is consumed. -/

/-- The subscheme of `ι.ker` is `G.G` transported along the iso `ι.toImage` (`ι` is a closed
immersion). Every property and degree comparison between `G` and its divisor goes through
this identity. -/
private theorem ker_subschemeι_eq (G : FiniteLocallyFreeSubgroup E) :
    G.ι.ker.subschemeι = inv G.ι.toImage ≫ G.ι := by
  rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι]

private theorem ker_prop (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (G : FiniteLocallyFreeSubgroup E) (hG : P (G.ι ≫ E.π)) :
    P (G.ι.ker.subschemeι ≫ E.π) := by
  rw [G.ker_subschemeι_eq, Category.assoc]
  exact (MorphismProperty.cancel_left_of_respectsIso P _ _).mpr hG

-- ATTACK (toRelEffCartierDiv): (1) the subscheme of `ι.ker` is NOT `G.G` itself, only
-- canonically isomorphic to it (via `ι.toImage`, an iso because `ι` is a closed
-- immersion) — all three properties and the degree must be transported along that iso,
-- which `ker_prop`/`toRelEffCartierDiv_degree` do; forgetting the transport and using
-- `D.finite := G.finite` would not typecheck (different morphisms). (2) this is a
-- retraction, not an equivalence of types: `ofRelEffCartierDiv ∘ toRelEffCartierDiv`
-- rebuilds the subscheme-of-the-kernel, an isomorphic but distinct total space; only
-- the ideal-level roundtrip (`toRelEffCartierDiv_ofRelEffCartierDiv`) is an identity.
set_option backward.isDefEq.respectTransparency.types false in
/-- The relative effective Cartier divisor underlying a finite locally free subgroup:
the closed subscheme cut out by `ι.ker` (KM 1.3.6 packages subgroups as divisors).
Properties transport along the canonical iso `G.G ≅ (ι.ker).subscheme`. -/
noncomputable def toRelEffCartierDiv (G : FiniteLocallyFreeSubgroup E) :
    RelEffCartierDiv E.π where
  ideal := G.ι.ker
  finite := ker_prop @IsFinite G G.finite
  flat := ker_prop @Flat G G.flat
  lfp := ker_prop @LocallyOfFinitePresentation G G.lfp

@[simp]
theorem toRelEffCartierDiv_ideal (G : FiniteLocallyFreeSubgroup E) :
    G.toRelEffCartierDiv.ideal = G.ι.ker :=
  rfl

/-- The divisor underlying a finite locally free subgroup satisfies the KM 1.3.6
divisor-subgroup predicate: factorisations through `(ι.ker).subscheme` and through `G`
are interchanged by the iso `ι.toImage`. -/
theorem toRelEffCartierDiv_isSubgroup (G : FiniteLocallyFreeSubgroup E) :
    G.toRelEffCartierDiv.IsSubgroup E := by
  intro T g
  obtain ⟨H, hH⟩ := G.subgroup g
  have hjeq : inv G.ι.toImage ≫ G.ι = G.ι.ker.subschemeι := G.ker_subschemeι_eq.symm
  refine ⟨H, fun P => (hH P).trans ?_⟩
  simp only [toRelEffCartierDiv_ideal]
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨h ≫ G.ι.toImage, ?_⟩
    rw [Category.assoc, Scheme.Hom.toImage_imageι]
    exact hh
  · rintro ⟨k, hk⟩
    refine ⟨k ≫ inv G.ι.toImage, ?_⟩
    rw [Category.assoc, hjeq]
    exact hk

/-- The degree of the underlying divisor is the rank of the subgroup (transport of
`finrank` along the iso `ι.toImage`). -/
theorem toRelEffCartierDiv_degree (G : FiniteLocallyFreeSubgroup E) (s : S) :
    G.toRelEffCartierDiv.degree s = G.rank s := by
  show (G.ι.ker.subschemeι ≫ E.π).finrank s = (G.ι ≫ E.π).finrank s
  rw [G.ker_subschemeι_eq, Category.assoc, Scheme.Hom.finrank_comp_left_of_isIso]

-- ATTACK (ofRelEffCartierDiv): (1) the `subgroup` field is `hD` VERBATIM — the KM 1.3.6
-- predicate `RelEffCartierDiv.IsSubgroup` was mirrored exactly so that this bridge is
-- definitional; if the two ∃-forms ever drift apart this definition breaks first (a
-- deliberate canary). (2) no rank hypothesis: a subgroup divisor of any (locally
-- constant) degree is a subgroup scheme; rank enters only through `HasRank`.
/-- A subgroup divisor (KM 1.3.6) *is* a finite locally free subgroup scheme: the
converse bridge, with total space the divisor's subscheme. The subgroup field is the
`IsSubgroup` hypothesis, definitionally. -/
noncomputable def ofRelEffCartierDiv (D : RelEffCartierDiv E.π) (hD : D.IsSubgroup E) :
    FiniteLocallyFreeSubgroup E where
  G := D.ideal.subscheme
  ι := D.ideal.subschemeι
  closedImmersion := inferInstance
  finite := D.finite
  flat := D.flat
  lfp := D.lfp
  subgroup := hD

/-- The two bridges are inverse at the divisor level (`ker_subschemeι`). -/
@[simp]
theorem toRelEffCartierDiv_ofRelEffCartierDiv (D : RelEffCartierDiv E.π)
    (hD : D.IsSubgroup E) :
    (ofRelEffCartierDiv D hD).toRelEffCartierDiv = D :=
  RelEffCartierDiv.ext (Scheme.IdealSheafData.ker_subschemeι _)

/-! ### Killed by the rank (KM 1.4.2 / Deligne, Oort–Tate) -/

/-- **KM 1.4.2 for subgroup schemes** (verbatim: *"Any finite locally free commutative
group-scheme of rank `N` is known to be killed by `N` (cf. [Oort–Tate])"*): every point
factoring through a subgroup scheme of constant rank `N` is annihilated by `N`.

Derived from the registered box
`RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors` (ExactOrder.lean — BB-DELIGNE,
stream OT, ticket T-OT0) through the divisor dictionary; no new box is minted. This is
the "killed by `N`" edge SG2's cyclicity layer consumes. -/
theorem HasRank.smul_eq_zero_of_factors {G : FiniteLocallyFreeSubgroup E} {N : ℕ}
    [NeZero N] (hG : G.HasRank N) {T : Scheme.{u}} (g : T ⟶ S) (P : E.Point g)
    (hP : P ∈ G.pointSubgroup g) : (N : ℤ) • P = 0 := by
  obtain ⟨h, hh⟩ := mem_pointSubgroup.mp hP
  refine RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors E
    G.toRelEffCartierDiv_isSubgroup
    (fun s => (G.toRelEffCartierDiv_degree s).trans (hG s)) g P
    ⟨h ≫ G.ι.toImage, ?_⟩
  show (h ≫ G.ι.toImage) ≫ G.ι.ker.subschemeι = P.1
  rw [Category.assoc, Scheme.Hom.toImage_imageι]
  exact hh

/-! ### Base change -/

private theorem baseChange_prop (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] (G : FiniteLocallyFreeSubgroup E)
    {T : Scheme.{u}} (g : T ⟶ S) (hG : P (G.ι ≫ E.π)) :
    P (pullback.snd G.ι (pullback.fst E.π g) ≫ pullback.snd E.π g) :=
  MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback G.ι (pullback.fst E.π g)).paste_vert
      (IsPullback.of_hasPullback E.π g)) hG

-- ATTACK (baseChange): (1) base change along an arbitrary `g : T ⟶ S` is safe for
-- finiteness (contrast the banked `flatPullback` counterexample `𝔾ₘ ↪ 𝔸¹_ℤₚ`, which
-- concerns pulling back along non-finite morphisms `C' ⟶ C` of *curves*, not along a
-- new base): here all three properties descend through the pasted pullback square
-- `G ×_S T = G ×_E (E ×_S T)`, with no hypothesis on `g`. (2) the total space is the
-- honest fibre product, so — unlike the divisor `baseChange` — no `ker`/`toImage`
-- transport is needed for the properties; the price is paid instead by the `subgroup`
-- field (sorried, T-SG1b): identifying `(E.baseChange g).Point g'` with
-- `E.Point (g' ≫ g)` compatibly with the group structure is exactly the base-change
-- spelling normalisation that parks `Point.asSection_zsmul` (GroupLaw.lean).
-- (3) iterated base change agrees with base change along the composite only up to
-- canonical isomorphism (as for divisors, `baseChange_baseChange_ideal`) — no
-- `baseChange_baseChange` identity is stated.
set_option backward.isDefEq.respectTransparency.types false in
/-- Base change of a finite locally free subgroup scheme along `g : T ⟶ S`: the total
space is `G ×_E (E ×_S T) = G ×_S T`, included in `(E.baseChange g).E = E ×_S T` by the
second projection. Finiteness, flatness and finite presentation descend through the
pasted pullback square; the subgroup condition is the T-SG1b sorry (see the module
docstring). -/
noncomputable def baseChange (G : FiniteLocallyFreeSubgroup E) {T : Scheme.{u}}
    (g : T ⟶ S) : FiniteLocallyFreeSubgroup (E.baseChange g) where
  G := pullback G.ι (pullback.fst E.π g)
  ι := pullback.snd G.ι (pullback.fst E.π g)
  closedImmersion := MorphismProperty.pullback_snd _ _ G.closedImmersion
  finite := baseChange_prop @IsFinite G g G.finite
  flat := baseChange_prop @Flat G g G.flat
  lfp := baseChange_prop @LocallyOfFinitePresentation G g G.lfp
  subgroup := by
    -- T-SG1b: the point-level base-change dictionary
    -- `(E.baseChange g).Point g' ≃+ E.Point (g' ≫ g)` (an `asSection`-type
    -- correspondence) transports `G.subgroup (g' ≫ g)`; factorisations correspond via
    -- the universal property of `pullback G.ι (pullback.fst E.π g)`. Blocked on the
    -- same spelling normalisation as `Point.asSection_zsmul` (GroupLaw.lean, PARKED).
    sorry

@[simp]
theorem baseChange_G (G : FiniteLocallyFreeSubgroup E) {T : Scheme.{u}} (g : T ⟶ S) :
    (G.baseChange g).G = pullback G.ι (pullback.fst E.π g) :=
  rfl

@[simp]
theorem baseChange_ι (G : FiniteLocallyFreeSubgroup E) {T : Scheme.{u}} (g : T ⟶ S) :
    (G.baseChange g).ι = pullback.snd G.ι (pullback.fst E.π g) :=
  rfl

/-- The rank of the base-changed subgroup at `t` is the rank at the image point
(`finrank` through the pasted pullback square). -/
theorem baseChange_rank (G : FiniteLocallyFreeSubgroup E) {T : Scheme.{u}} (g : T ⟶ S)
    (t : T) : (G.baseChange g).rank t = G.rank (g t) := by
  show Scheme.Hom.finrank
      (pullback.snd G.ι (pullback.fst E.π g) ≫ pullback.snd E.π g) t =
    Scheme.Hom.finrank (G.ι ≫ E.π) (g t)
  exact Scheme.Hom.finrank_of_isPullback _ _ _ _
    ((IsPullback.of_hasPullback G.ι (pullback.fst E.π g)).paste_vert
      (IsPullback.of_hasPullback E.π g)) t

/-- Constant rank is stable under base change (the shape SG2's fppf-local cyclicity
needs: "rank `N`" may be checked after an fppf cover). -/
theorem HasRank.baseChange {G : FiniteLocallyFreeSubgroup E} {r : ℕ}
    (hG : G.HasRank r) {T : Scheme.{u}} (g : T ⟶ S) :
    (G.baseChange g).HasRank r :=
  fun t => (G.baseChange_rank g t).trans (hG _)

end FiniteLocallyFreeSubgroup

/-! ### The leading example: `E[N]` (kernel-style constructor)

The kernel of `[N] : E ⟶ E` — the existing `E.torsion N` pullback — as a
`FiniteLocallyFreeSubgroup`. More general kernels (of isogenies, of `F`/`V` in
characteristic `p`) will follow the same recipe once their sources exist; the
`torsionSubgroup` fields below are the template. -/

variable (E : EllipticCurve S)

set_option backward.isDefEq.respectTransparency.types false in
/-- `E[N] ⟶ S` is locally of finite presentation: base change of
`MulByHom.locallyOfFinitePresentation` (the `lfp` sibling of `torsionπ_isFinite` /
`torsionπ_flat`, T-B4). -/
theorem torsionπ_locallyOfFinitePresentation (N : ℕ) :
    LocallyOfFinitePresentation (E.torsionπ N) := by
  have h := MulByHom.locallyOfFinitePresentation E N
  exact MorphismProperty.pullback_snd _ _ h

/-- A point of `E` factors through `E[N] ⟶ E` iff it is killed by `N` — the kernel
universal property of `E.torsion N` in factoring form (`pointToTorsion` packaged as the
membership `torsionSubgroup` needs). Holds for every `N`, including `N = 0`
(`E[0] = E`, and `0 • P = 0` always). -/
theorem torsionι_factors_iff (N : ℕ) {T : Scheme.{u}} (g : T ⟶ S) (P : E.Point g) :
    (∃ h : T ⟶ E.torsion N, h ≫ E.torsionι N = P.1) ↔ (N : ℤ) • P = 0 := by
  rw [E.smul_eq_zero_iff_comp_mulByHom]
  constructor
  · rintro ⟨h, hh⟩
    have hcond : E.torsionι N ≫ E.mulByHom (N : ℤ) = E.torsionπ N ≫ E.zero :=
      pullback.condition
    have hπ : h ≫ E.torsionπ N = g := by
      rw [← E.torsionι_π N, ← Category.assoc, hh, P.2]
    calc P.1 ≫ E.mulByHom (N : ℤ)
        = (h ≫ E.torsionι N) ≫ E.mulByHom (N : ℤ) := by rw [hh]
      _ = h ≫ E.torsionι N ≫ E.mulByHom (N : ℤ) := Category.assoc _ _ _
      _ = h ≫ E.torsionπ N ≫ E.zero := by rw [hcond]
      _ = (h ≫ E.torsionπ N) ≫ E.zero := (Category.assoc _ _ _).symm
      _ = g ≫ E.zero := by rw [hπ]
  · intro hP
    exact ⟨E.pointToTorsion P hP, E.pointToTorsion_torsionι P hP⟩

-- ATTACK (torsionSubgroup): (1) `N = 0` is rightly excluded by `[NeZero N]`:
-- `E[0] = ker [0] = E` itself, which is proper of relative dimension 1, never finite
-- over a nonempty base — `torsionπ_isFinite` genuinely needs `NeZero`. (2) `N = 1`
-- sanity: `E[1]` is the zero subgroup, rank `1 = 1²` — the trivial subgroup is an
-- honest inhabitant, not a degenerate case. (3) in char `p ∣ N` the subscheme `E[N]`
-- is non-étale/non-reduced (e.g. `Ker F ⊆ E[p]`), but nothing here assumes
-- reducedness or étaleness — only finite locally free (KM's point). (4) NO new sorry:
-- each field is discharged by a proved Torsion.lean theorem (T-B3/T-B4 + the
-- `lfp` sibling above) or proved here (`torsionι_factors_iff`); the upstream boxes
-- BB-QF/BB-FLAT remain where the board registered them.
/-- **The `N`-torsion subgroup scheme `E[N] ⊆ E`** (KM 2.3.1: finite locally free of
rank `N²`), as the leading example of a `FiniteLocallyFreeSubgroup`: the kernel-style
constructor applied to `[N]`, with total space the existing pullback `E.torsion N`.

Fields: closed immersion = T-B3 (`torsionι_isClosedImmersion`); finite/flat = T-B4
(`torsionπ_isFinite`/`torsionπ_flat`, resting on the registered boxes BB-QF/BB-FLAT in
Torsion.lean); subgroup condition proved via the kernel universal property
(`torsionι_factors_iff`: the factoring points are exactly `Submodule.torsionBy ℤ _ N`). -/
noncomputable def torsionSubgroup (N : ℕ) [NeZero N] : FiniteLocallyFreeSubgroup E where
  G := E.torsion N
  ι := E.torsionι N
  closedImmersion := E.torsionι_isClosedImmersion N
  finite := by rw [E.torsionι_π N]; exact E.torsionπ_isFinite N
  flat := by rw [E.torsionι_π N]; exact E.torsionπ_flat N
  lfp := by rw [E.torsionι_π N]; exact E.torsionπ_locallyOfFinitePresentation N
  subgroup := fun T g =>
    ⟨(Submodule.torsionBy ℤ (E.Point g) (N : ℤ)).toAddSubgroup, fun P => by
      rw [Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff]
      exact (E.torsionι_factors_iff N g P).symm⟩

@[simp]
theorem torsionSubgroup_G (N : ℕ) [NeZero N] :
    (E.torsionSubgroup N).G = E.torsion N :=
  rfl

@[simp]
theorem torsionSubgroup_ι (N : ℕ) [NeZero N] :
    (E.torsionSubgroup N).ι = E.torsionι N :=
  rfl

/-- The point subgroup of `E[N]` is the `N`-torsion of the point group (the
`torsionPointsEquiv` statement in `AddSubgroup` form). -/
theorem torsionSubgroup_pointSubgroup (N : ℕ) [NeZero N] {T : Scheme.{u}} (g : T ⟶ S) :
    (E.torsionSubgroup N).pointSubgroup g =
      (Submodule.torsionBy ℤ (E.Point g) (N : ℤ)).toAddSubgroup :=
  AddSubgroup.ext fun P => by
    rw [FiniteLocallyFreeSubgroup.mem_pointSubgroup, Submodule.mem_toAddSubgroup,
      Submodule.mem_torsionBy_iff]
    exact E.torsionι_factors_iff N g P

/-- **KM 2.3.1, rank part, in subgroup-scheme form**: `E[N]` has constant rank `N²`
(`torsion_rank` transported along `torsionι_π`). This is the input SG2's Γ₀(N) layer
feeds to `HasRank.smul_eq_zero_of_factors` — note `E[N]` has rank `N²`, so it is
killed by `N²`; being killed by `N` is the finer `torsionι_factors_iff`. -/
theorem torsionSubgroup_hasRank (N : ℕ) [NeZero N] :
    (E.torsionSubgroup N).HasRank (N ^ 2) := fun s => by
  show (E.torsionι N ≫ E.π).finrank s = N ^ 2
  rw [E.torsionι_π N]
  exact E.torsion_rank N s

end EllipticCurve

end ModularCurves
