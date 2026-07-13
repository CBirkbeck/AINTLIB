# Decomposition: [T-E-OMEGA] route R1 — the invariant differential `ω_{E/S}`

**Author**: STREAM-OMEGA seat, 2026-07-13. **Charter**: inbox/STREAM-OMEGA.md (v10.179).

## 0′. v10.180 re-steer reconciliation (2026-07-13, mid-session)

Coordinator steer: *"ω2 must CONSUME the invertible-sheaf infra (codex's
`IsInvertible.isLocallyFree` + trivialization layer, arriving via codex-merge tranche-1),
not rebuild it; build on our `Picard/InvertibleSheaf.lean`."* Reconciliation with the
work already landed:

- **No rebuild happened.** `omegaModules_isInvertible` targets the shared
  `Picard/InvertibleSheaf.lean` predicate `Scheme.Modules.IsInvertible` verbatim, and the
  proof route reuses `Picard/IdealModule.lean`'s `isIso_of_bijective_app_on_basis` +
  `restrictFunctorIsoPullback` assembly. Nothing in the OMEGA files restates
  `IsInvertible`, `isLocallyFree`, `FiniteAffineCover`, or `BaseCechFlat` (codex's layer —
  not yet on our line; grep-verified absent).
- **Direction is complementary, not duplicated.** Codex's tranche is the *extraction*
  direction (from `IsInvertible`, produce locally-free/trivialization data for arbitrary
  invertible sheaves). `UnitCocycleSheaf` is the *construction* direction (from a Čech
  unit cocycle, produce a module sheaf and prove it `IsInvertible`) plus the
  cocycle-model-specific sections API (`sections V` = compatible families, definitionally)
  that ω3/ω4/ω5 compute with — the transition-unit arithmetic (`u_self`/`u_cocycle`
  consumption, `Compat` transport, basis pullback) has no counterpart in an abstract
  invertible-sheaf layer. When tranche-1 lands, `IsInvertible (omegaModules G)` composes
  with codex's `IsInvertible.isLocallyFree` with no interface work.
- **Sequencing conformance**: ω1 (B2, the transition-cocycle engine) was completed first
  and is independent, as steered; ω2 as landed is ALSO independent of the codex tranche
  (it needs only the already-on-line `Picard/InvertibleSheaf.lean`), so no gate is
  actually crossed. Flagged for the coordinator at tranche-1: if codex's trivialization
  API and `UnitCocycle.sectionsEquivOfLE` overlap for the *specific* cocycle bundles, the
  dedup is a cleanup-lane pass on top of the merge; `ForMathlib/UnitCocycleSheaf.lean` is
  additionally a `/mathlibable` candidate (mathlib has no cocycle→bundle constructor).
**Board section**: tickets.md [T-E-OMEGA] (~2209). **Route**: R1 (atlas-glued), UNGATED —
T-W7.1b = `pointedIso_exists_variableChange` proven sorry-free (`EllipticCurve/Comparison.lean:162`).

## 0. Substrate scan (all verified at source, 2026-07-13)

| Ingredient | Location | Status |
|---|---|---|
| `pointedIso_exists_variableChange` (1b, existence) | `EllipticCurve/Comparison.lean:162` | PROVEN |
| `projModelVCIso_injective` (1b, uniqueness) | `EllipticCurve/Comparison.lean:226` | PROVEN |
| `projModelVCIso_one` / `_mul` (cocycle laws) | `ModelVariableChange.lean:604/648` | PROVEN |
| `projModelVCIso_map` (base-change naturality) | `ModelVariableChange.lean:564` | PROVEN |
| `projModelBaseChange` + `isPullback_projModelBaseChange` | `WeierstrassModel.lean:1884/2621` | PROVEN |
| `WeierstrassAtlasData` + `EllipticCurveGeom.atlas` | `WeierstrassAtlasBundle.lean:27/50` | PROVEN |
| `VariableChange.map`, `mapHom`, `map_variableChange` | mathlib `AlgebraicGeometry/EllipticCurve/VariableChange.lean:262/294/305` | mathlib |
| `Scheme.Modules` (`SheafOfModules X.ringCatSheaf`) | mathlib `AlgebraicGeometry/Modules/Sheaf.lean:39` | mathlib |
| `PresheafOfModules.ofPresheaf` (Ab-presheaf + semilinear maps constructor) | mathlib `Algebra/Category/ModuleCat/Presheaf.lean:188` | mathlib |
| unique gluing (`existsUnique_gluing`, `isSheaf_iff_isSheafUniqueGluing`) | mathlib `Topology/Sheaves/SheafCondition/UniqueGluing.lean` | mathlib |
| `RingedSpace.isUnit_of_isUnit_germ` (locally-unit ⟹ unit) | mathlib `Geometry/RingedSpace/Basic.lean:94` | mathlib |
| `SheafOfModules.IsLocallyFree` (stacks 01C6) | mathlib `Algebra/Category/ModuleCat/Sheaf/LocallyFree.lean` | mathlib (site-instance risk over `(J.over X)`, see A8) |
| `negModelHom` (+π/zero compat, involution) | `GroupLawConstruction.lean:347` | PROVEN |
| `EllObj`/`EllHom`/`ModuliProblem` | `Moduli/EllCategory.lean:38/59/91` | PROVEN |

**Board-scan correction**: the v10.27 substrate scan said mathlib has "no line-bundle
predicate, no glue-of-modules API". Partially stale: mathlib NOW has
`SheafOfModules.IsLocallyFree` (Nugent, 2026) and a rich `Scheme.Modules` functoriality
API (`pullback`/`pushforward`/`restrictFunctor`/`restrictAppIso`). Still absent: gluing of
sheaves from cocycle data, and `Ω¹`. The construction below therefore builds the glued
invertible sheaf **directly as a subsheaf of a product of pushforwards** (compatible-family
model), which avoids any glue-of-isomorphisms bookkeeping.

## 1. The mathematical object and the design decision

**Sources.** KM §2.2 (p. 68: `ω_{E/S} := π_*(Ω¹_{E/S(log ∞)})`-free presentation; the T-A4
quote mine, tickets.md:7769: *"f_*(I⁻²(0)) is free on 1, x with x² a basis of the rank-one
quotient"*, giving the local freeness of the pushforward sheaves on a Weierstrass chart);
KM 4.6.2 verbatim (`.mathlib-quality/km47-source-quotes.md` §4): *"E/S ↦ pairs (φ₂, ω)
consisting of an S-group-scheme isomorphism φ₂ : (ℤ/2ℤ)² ≅ E[2] together with an S-basis ω
of ω_{E/S} for which the adapted x satisfies x(P₂) = 0, x(Q₂) = 1. The corresponding
S-scheme 𝒫_{E/S} is concentrated over S[1/2], over which it is a finite etale
GL(2, ℤ/2ℤ) × {±1} torsor."* Hida GME §2.2 (Hodge bundle); Silverman AEC III §1 Table 1.2:
the invariant differential `ω = dx/(2y + a₁x + a₃)` of a Weierstrass model transforms under
the variable change `x = u²x' + r, y = u³y' + u²sx' + t` by the **unit `u`**
(`ω = u⁻¹·ω'`, i.e. the chart bases differ by the transition unit).

**What the classical object is.** For an elliptic curve `E/S`, `ω_{E/S}` is the invertible
`𝒪_S`-sheaf `π_*Ω¹_{E/S}`. On each Weierstrass chart `(U, W, e)` of the atlas it is free of
rank 1 with canonical basis `dx/(2y + a₁x + a₃)`; on chart overlaps the two canonical bases
differ by the unit `u` of the comparison variable change (Silverman III Table 1.2). Neither
`Ω¹` nor the cotangent complex exists in mathlib (verified again this session), so the
project cannot *derive* this presentation — but the presentation **determines the object up
to canonical isomorphism**, and every consumer in this repo (T-E12/T-E13/T-E14 ω-data, T-A4
trivialization, the modular-forms Hodge bundle) consumes exactly the presentation:

**Design decision (Lean ↔ source match, global).** We DEFINE `ω_{E/S}` as the invertible
sheaf glued from the trivial line bundles on the Weierstrass atlas charts along the
transition cocycle `u_{ij} :=` (unit of the comparison variable change), i.e. the sheaf of
"families that transform like the classical chart bases". This is faithful to the sources
in the precise sense: the classical `π_*Ω¹` carries canonical chart trivializations by
`dx/(2y+a₁x+a₃)` whose transition matrix is exactly `u_{ij}` (Silverman III Table 1.2), so
the classical sheaf and ours represent the same twisted product; an `S`-basis of one is an
`S`-basis of the other. KM's Legendre datum "an S-basis ω of ω_{E/S}" becomes "a global
section that is a unit in every chart" (leaf A7/B6). The KM {±1}-action on the ω-datum is
the `(-1 : Γ(S)ˣ)`-scaling of bases (leaf A7); the fact that the elliptic-curve inversion
`[-1]` induces it is recorded via the `negVC` identification (leaf B8) and consumed by
T-E14's proof, not by its statement.

**Why not R2 (conormal `zero^*(I/I²)`).** R2 needs `IdealSheafData → Scheme.Modules`
conversion (absent), closed-immersion instances for the zero section, the conormal
computation on the `Z`-chart, and *still* needs the Weierstrass basis computation to exhibit
invertibility — strictly more new infra (board est. 600–900 ln), and its output would still
be consumed through chart trivializations. R1 confirmed.

## 2. Architecture: two new files

### PART A — `ModularCurves/ForMathlib/UnitCocycleSheaf.lean` (generic, mathlib-able)

For an arbitrary scheme `X`: from an open cover `U : ι → X.Opens` and a Čech 1-cocycle of
units `u i j ∈ Γ(X, U i ⊓ U j)ˣ` (normalized: `u i i = 1`; cocycle on triple overlaps),
build the invertible sheaf of modules it glues. **Model**: the "compatible families"
subsheaf of `∏ i, (ι_i)_* 𝒪_{U i}` — concretely, sections over `V` are families
`b : ∀ i, Γ(X, V ⊓ U i)` with `b i = u i j · b j` on `V ⊓ U i ⊓ U j`. No abstract gluing
theorem is used; the sheaf property reduces to that of `𝒪_X` componentwise. This is
`Stacks 01AJ`-style twisted-product data specialized to rank 1; nothing elliptic in it.

### PART B — `ModularCurves/EllipticCurve/InvariantDifferential.lean` (the ω-stream)

For `G : EllipticCurveGeom S`: package "pointed Weierstrass presentations over an affine
open" (`LocalPresentation`), produce the **unique comparison variable change** between any
two presentations over the same affine (1b + faithfulness), gain the cocycle laws for free
from uniqueness, glue the comparison units over the (possibly non-affine) pairwise
intersections of the atlas, feed PART A, and define
`omegaModules G : S.Modules`. Then bases, base-change transport along `EllHom` cartesian
squares (functor form, what T-E12/13/14 quantify over), and the negation unit.

**Boundary discipline (charter)**: consumes `pointedIso_exists_variableChange` and the
`ModelVariableChange`/`WeierstrassModel` API; touches NOTHING in `Comparison.lean`/
`PoleSheaf.lean` (CODEX worker's); all new decls in the two new files.

## 3. Leaves — PART A (all in `ForMathlib/UnitCocycleSheaf.lean`, namespace `ModularCurves`)

Notation: `resLE : W' ≤ W → Γ(X, W) →+* Γ(X, W')` is `X.presheaf.map (homOfLE h).op`
(with `CommRingCat.Hom.hom`); `resUnit` its `Units.map`.

### [T-OM-A1] `UnitCocycle` + the sections module
```lean
structure UnitCocycle (X : Scheme.{u}) where
  ι : Type u
  U : ι → X.Opens
  covers : ∀ x : X, ∃ i, x ∈ U i
  u : ∀ i j, Γ(X, U i ⊓ U j)ˣ
  u_self : ∀ i, u i i = 1
  u_cocycle : ∀ i j k, resUnit (h₁ : U i ⊓ U j ⊓ U k ≤ U i ⊓ U j) (u i j) *
    resUnit (h₂ : … ≤ U j ⊓ U k) (u j k) = resUnit (h₃ : … ≤ U i ⊓ U k) (u i k)

def UnitCocycle.Compatible (c : UnitCocycle X) (V : X.Opens)
    (b : ∀ i, Γ(X, V ⊓ c.U i)) : Prop := ∀ i j,
  resLE _ (b i) = (resUnit _ (c.u i j) : Γ(X, V ⊓ c.U i ⊓ c.U j)) * resLE _ (b j)
  -- restrictions to V ⊓ U i ⊓ U j (≤ V ⊓ U i, ≤ V ⊓ U j, ≤ U i ⊓ U j resp.)

def UnitCocycle.sections (c : UnitCocycle X) (V : X.Opens) : Type u :=
  {b : ∀ i, Γ(X, V ⊓ c.U i) // c.Compatible V b}
-- + AddCommGroup (c.sections V), Module Γ(X, V) (c.sections V) (componentwise via resLE)
```
**Prose**: `Compatible` is closed under `+`, `-`, `0`, and the `Γ(V)`-action because each
condition is `RingHom`-linear in `b` (restrictions are ring maps; multiplication by a fixed
unit is additive and commutes with the scalar restriction). **Dischargeable from**: pure
`Subtype`/`Pi` algebra; `Units.map`; no gaps. **Generality**: `Scheme.{u}` (a
`LocallyRingedSpace` version is a trivial generalization left for mathlib upstreaming;
every consumer is a scheme).
**Source anchor**: Stacks 01AJ (glueing sheaves data), specialized: the compatible-family
model of the twisted product. Match: our `sections V` = `{(s_i) ∈ ∏ Γ(V ∩ U_i) : s_i = u_{ij} s_j}`,
verbatim the Čech description of the glued invertible sheaf's sections.

### [T-OM-A2] restriction maps + the `Ab`-presheaf + `PresheafOfModules`
```lean
def UnitCocycle.sectionsMap (c) {V' V : X.Opens} (h : V' ≤ V) :
    c.sections V →+ c.sections V'          -- componentwise resLE (V' ⊓ U i ≤ V ⊓ U i)
def UnitCocycle.presheafAb (c) : (Opens X)ᵒᵖ ⥤ Ab           -- obj := AddCommGrp.of (sections)
def UnitCocycle.presheafOfModules (c) : PresheafOfModules X.ringCatSheaf.val
    -- via PresheafOfModules.ofPresheaf: Module instances from A1 + semilinearity
```
**Prose**: restriction preserves compatibility (restrict the defining equation; two
`resLE`s compose by `X.presheaf.map_comp`). Functoriality: `Subtype.ext` + `map_id/map_comp`
of `𝒪_X`. Semilinearity `sectionsMap h (r • b) = resLE h r • sectionsMap h b`: componentwise,
`resLE` multiplicative. **Dischargeable**: mechanical; the only care point is
`ringCatSheaf.val` sections vs `Γ(X, ·)` coercions (`Scheme.ringCatSheaf` is
`X.presheaf ⋙ forget₂ CommRingCat RingCat`-sheafed; its sections carry the same carrier —
supply `rfl`-level simp lemmas). No gaps.

### [T-OM-A3] sheaf condition + the bundled `X.Modules` object + sections API
```lean
theorem UnitCocycle.isSheaf (c) : TopCat.Presheaf.IsSheaf c.presheafAb
noncomputable def UnitCocycle.lineBundle (c) : X.Modules   -- ⟨presheafOfModules, isSheaf⟩
def UnitCocycle.lineBundleSectionsEquiv (c V) : Γ(c.lineBundle, V) ≃ₗ[Γ(X,V)] c.sections V
```
**Prose (sheaf)**: via `isSheaf_iff_isSheafUniqueGluing` (Ab is a concrete category with
limits, `forget` preserves & reflects): a compatible family of `c.sections (V l)` over a
cover `V = ⨆ V l` glues componentwise — for fixed `i`, the `b^l i ∈ Γ(V l ⊓ U i)` form a
compatible family over the cover `V ⊓ U i = ⨆ (V l ⊓ U i)` of `𝒪_X` (as a sheaf of types
via `existsUnique_gluing'`), producing `b i`; the glued family is `Compatible` because the
compatibility equation holds after restriction to each `V l ⊓ …` and `𝒪_X` is separated
(`eq_of_locally_eq`-style, i.e. the uniqueness half of gluing on the zero section);
uniqueness is componentwise separation. **Dischargeable**: mathlib's UniqueGluing +
CommRingCat forget plumbing; standard but the most fiddly PART-A leaf. No mathematical gap.

### [T-OM-A4] chart trivialization
```lean
def UnitCocycle.trivSection (c) (k : c.ι) {V : X.Opens} (hV : V ≤ c.U k) : c.sections V
    -- i-component: resUnit (V ⊓ U i ≤ U i ⊓ U k) (c.u i k) * (resLE (V ⊓ U i ≤ V) applied to 1) — i.e. the family (u i k)|
def UnitCocycle.sectionsEquivOfLE (c) (k) (hV : V ≤ c.U k) :
    c.sections V ≃ₗ[Γ(X,V)] Γ(X, V)     -- b ↦ (V ⊓ U k = V)-transport of (b k); inverse g ↦ g • trivSection
theorem UnitCocycle.sectionsEquivOfLE_natural (c k) {V' V} (hV' : V' ≤ V) (hV : V ≤ c.U k) :
    (sectionsEquivOfLE c k (hV'.trans hV)) ∘ sectionsMap hV' = resLE hV' ∘ sectionsEquivOfLE c k hV
```
**Prose**: forward `b ↦ b k` transported along `V ⊓ U k = V` (`inf_eq_left.mpr`); inverse
`g ↦ (i ↦ u i k · g)`; the two compatibility checks are the cocycle law restricted to
`V ⊓ U i ⊓ U j ≤ U i ⊓ U j ⊓ U k` and left-inverse is the family's own compatibility at
`(i, k)` (note `V ⊓ U i ≤ U i ⊓ U k` since `V ≤ U k`), right-inverse is `u_self`.
**This is where `u_self` and `u_cocycle` are consumed; the construction is the
invertibility.** **Dischargeable**: A1-A2 + `Opens` lattice + eqToHom-on-opens transport
(`X.presheaf.map (eqToHom …)`); no gaps.
**Source anchor**: KM p. 68 loc.cit. — the chart-freeness of `ω`; match: `sectionsEquivOfLE`
IS the statement "`ω|_V` is free of rank 1 on the chart basis" with the chart basis =
`trivSection` (the family `(u i k)_i` = the coordinates of the classical `dx/(2y+a₁x+a₃)`
of chart `k` expressed in every chart `i`).

### [T-OM-A5] bases and the torsor structure
```lean
def UnitCocycle.IsBasis (c) {V} (b : c.sections V) : Prop := ∀ i, IsUnit (b.1 i)
theorem isBasis_trivSection …                                   -- the chart section is a basis
theorem isBasis_smul_iff (g : Γ(X,V)ˣ) : IsBasis (g • b) ↔ IsBasis b
theorem exists_unique_unit_smul (hb : IsBasis b) (b' : c.sections V) :
    ∃! g : Γ(X, V), g • b = b'                                  -- and g is a unit iff b' is a basis
theorem isBasis_iff_isUnit_sectionsEquivOfLE …                  -- over V ≤ U k
```
**Prose (torsor)**: given a basis `b` and any `b'`, the ratios `g_i := b'_i · (b_i)⁻¹` on
`V ⊓ U i` agree on double overlaps (both `b, b'` transform by the same `u i j`, which
cancels), hence glue to `g ∈ Γ(X, V)` over the cover `{V ⊓ U i}` of `V` (A3's gluing);
`g • b = b'` holds componentwise; uniqueness by separation + `b_i` unit. **Dischargeable**:
`𝒪_X` gluing + `Units` algebra; no gaps.
**Source anchor**: KM 4.6.2's "{±1} torsor" factor + T-A4's v9.4 torsor form. Match: the
`Γ(X,V)ˣ`-action on bases is simply transitive — the trivialization/`𝔾ₘ`-torsor statement
the board calls "ω3 = T-A4's trivialization, one construction, three consumers". The
{±1}-action of KM 4.6.2 is this action restricted to `⟨-1⟩ ≤ Γ(S)ˣ`.

### [T-OM-A6] glueing a unit over an open from affine-local units (generic helper)
```lean
theorem Scheme.exists_unit_glue (X : Scheme.{u}) (W : X.Opens)
    (data : ∀ V : X.affineOpens, V.1 ≤ W → Γ(X, V.1)ˣ)
    (compat : ∀ (V V' : X.affineOpens) (hV : V.1 ≤ W) (hV' : V'.1 ≤ W) (h : V'.1 ≤ V.1),
      resUnit h (data V hV) = data V' hV') :
    ∃! g : Γ(X, W)ˣ, ∀ (V : X.affineOpens) (hV : V.1 ≤ W), resUnit hV g = data V hV
```
**Prose**: affine opens form a basis (`AlgebraicGeometry.isBasis_affine_open`), so `W` is
covered by affines `V ≤ W`; the underlying sections of `data` form a compatible family
(compat on `V' = V ∩ V''`-refinements — pairwise agreement via the basis, since two affines'
intersection is covered by affines on which both restrict to the data); glue to
`g₀ ∈ Γ(X, W)` by `existsUnique_gluing'`; `g₀` is a unit because it is locally a unit
(`RingedSpace.isUnit_of_isUnit_germ` via germs, each germ factors through some affine `V`);
uniqueness by separation. **Dischargeable**: mathlib; the pairwise-agreement-from-basis
step is the only subtle point (state `compat` against ALL pairs with `V' ≤ V` as above —
then agreement of `data V` and `data V''` on `V ∩ V''` follows by restricting both to each
affine inside `V ∩ V''` and separation). No gaps.

### [T-OM-A7] cocycle comparison (`Compat`) and section transport
```lean
structure UnitCocycle.Compat (c c' : UnitCocycle X) where
  w : ∀ (i : c.ι) (j : c'.ι), Γ(X, c.U i ⊓ c'.U j)ˣ
  left : ∀ i i' j, (on c.U i ⊓ c.U i' ⊓ c'.U j) res (c.u i i') * res (w i' j) = res (w i j)
  right : ∀ i j j', (on c.U i ⊓ c'.U j ⊓ c'.U j') res (w i j) * res (c'.u j j') = res (w i j')
noncomputable def UnitCocycle.Compat.sectionsEquiv (κ : Compat c c') (V : X.Opens) :
    c'.sections V ≃ₗ[Γ(X,V)] c.sections V
theorem Compat.isBasis_sectionsEquiv_iff …
```
**Prose**: given `b' ∈ c'.sections V`, define the `i`-component of the image on `V ⊓ c.U i`
by gluing (A6-style, but for arbitrary sections — reuse A3's componentwise gluing) the
family `res (w i j) * res (b' j)` over the cover `{V ⊓ c.U i ⊓ c'.U j}_j` of `V ⊓ c.U i`
(matching on overlaps by `right`); the resulting family is `c`-Compatible by `left`;
inverse via the inverse compat `κ⁻¹ := (w i j ↦ (w j i)⁻¹ — after the two laws are shown
symmetric)`, or directly by uniqueness of gluings. Preserves bases (units glue to units).
**Dischargeable**: A1-A6 machinery; no new math. **Note**: this is "cohomologous cocycles
give isomorphic bundles" in the direction needed; we never need H¹ machinery.

### [T-OM-A8] (corollary, RISK-FLAGGED, non-load-bearing) `IsLocallyFree`
```lean
theorem UnitCocycle.lineBundle_isLocallyFree (c) : c.lineBundle.IsLocallyFree
```
**Prose**: the covering sieve of the `U i` + `sectionsEquivOfLE` gives one generating
section over each `U i`… wait — trivialization is over `V ≤ U i` (all `V`), in particular
over `U i` itself (`le_rfl`); `LocalGeneratorsData` with `X i := U i`, generator :=
`trivSection i le_rfl`, `IsLocallyFreeData` from the equiv. **Risk**: the
`(J.over X).HasSheafCompose/HasWeakSheafify/WEqualsLocallyBijective` instance chain for
`J = Opens.grothendieckTopology S` must be found/derived; mathlib's generic instances
(`Sites/LocallyBijective.lean:153`) should fire but are untested here. Not consumed by any
PART-B leaf; if instances fight, park it (its own ticket, never blocks the stream).

## 4. Leaves — PART B (`EllipticCurve/InvariantDifferential.lean`)

Throughout `S : Scheme.{u}`, `G : EllipticCurveGeom S`. Sections ring maps between opens
of `S` are `resLE`; for `V' ≤ V` affine opens, `Algebra Γ(S,V) Γ(S,V')` via
`(resLE …).toAlgebra` (`letI`, house style per `locallyWeierstrass_projModel`).

### [T-OM-B1] `LocalPresentation` + atlas presentations
```lean
structure LocalPresentation (G : EllipticCurveGeom S) (V : S.affineOpens) where
  W : WeierstrassCurve Γ(S, V.1)
  elliptic : W.IsElliptic
  e : pullback G.π V.1.ι ≅ projModel W
  compat_π : e.hom ≫ projModelπ W = pullback.snd G.π V.1.ι ≫ V.2.isoSpec.hom
  compat_zero : (V.2.isoSpec.inv ≫ pullback.lift (V.1.ι ≫ G.zero) (𝟙 _) (…)) ≫ e.hom
      = projModelZero W
noncomputable def WeierstrassAtlasData.presentation (A : WeierstrassAtlasData G) (i : A.ι) :
    LocalPresentation G (A.U i)      -- repackage the atlas fields
```
**Prose**: pure repackaging of `WeierstrassAtlasData`'s per-index fields (same five
components, same compatibilities — copied verbatim from `WeierstrassAtlasBundle.lean:27-46`).
**Dischargeable**: definitional. **Generality**: per-affine-open; the affineness is forced
by 1b (the comparison theorem lives over a ring).

### [T-OM-B2] the comparison variable change of two presentations + laws
```lean
noncomputable def LocalPresentation.pointedIso (P Q : LocalPresentation G V) :
    projModel P.W ≅ projModel Q.W := P.e.symm ≪≫ Q.e
theorem LocalPresentation.pointedIso_π / _zero …        -- from compat_π/compat_zero of P, Q
noncomputable def LocalPresentation.transVC (P Q : LocalPresentation G V) :
    VariableChange Γ(S, V.1)                            -- 1b's C : transVC P Q • Q.W = P.W
theorem transVC_smul (P Q) : (transVC P Q) • Q.W = P.W
theorem transVC_spec (P Q) : (P.pointedIso Q).hom = eqToHom (…) ≫ (projModelVCIso (transVC P Q) Q.W).hom
theorem transVC_unique (P Q) (C) (hC : C • Q.W = P.W)
    (h : (P.pointedIso Q).hom = eqToHom (…) ≫ (projModelVCIso C Q.W).hom) : C = transVC P Q
theorem transVC_self (P) : transVC P P = 1
theorem transVC_trans (P Q R') : transVC P Q * transVC Q R' = transVC P R'
noncomputable def LocalPresentation.transUnit (P Q) : Γ(S, V.1)ˣ := (transVC P Q).u
-- + transUnit_self, transUnit_trans (from the VC laws; (C*C').u = C.u * C'.u by VariableChange.mul_def)
```
**Prose**: existence+spec from `pointedIso_exists_variableChange` applied to
`P.pointedIso Q` (π/zero-compat composites: `P.e.symm` reverses `P.compat_π/zero`, then
`Q.e`'s compat re-points — the `isoSpec` legs cancel); `transVC_self`: `pointedIso P P =
Iso.refl` (by `Iso.symm_self_id`-style simp), and `projModelVCIso_one` says `C = 1`
satisfies the defining property, so uniqueness (`projModelVCIso_injective` in the shape
`transVC_unique`) pins `transVC P P = 1`. `transVC_trans`: both sides act on `R'.W` giving
`P.W` (`mul_smul`); the defining isos compose (`pointedIso P Q ≪≫ pointedIso Q R' =
pointedIso P R'` — `e.symm ≪≫ (Q.e ≪≫ Q.e.symm) ≪≫ …` cancels); `projModelVCIso_mul`
rewrites the product's iso as the composite of the factors' isos (eqToHom bookkeeping);
uniqueness concludes. **Dischargeable**: Comparison.lean + ModelVariableChange.lean
+ category algebra; no gaps. **Source**: Silverman III.3.1(b) (isomorphisms of Weierstrass
models are variable changes — verbatim the 1b statement's classical form); KM 2.2.5
("two Weierstrass presentations differ by a variable change", the T-A4 quote).
**Lean ↔ source**: `transVC` is *the* variable change of KM 2.2.5 for the two chart
presentations; `transUnit` is its `u`, the number by which the two classical chart bases
`dx/(2y+a₁x+a₃)` differ (Silverman III Table 1.2).

### [T-OM-B3] transport of a presentation along a cartesian pointed square (+ restriction)
```lean
noncomputable def LocalPresentation.transport
    {S' S : Scheme.{u}} {G' : EllipticCurveGeom S'} {G : EllipticCurveGeom S}
    (f : S' ⟶ S) (t : G'.E ⟶ G.E)      -- with (hsq : IsPullback t G'.π G.π f) (hz : G'.zero ≫ t = f ≫ G.zero)
    {V : S.affineOpens} (P : LocalPresentation G V)
    {V' : S'.affineOpens} (hV' : V'.1 ≤ f ⁻¹ᵁ V.1) :
    LocalPresentation G' V'
-- W-component: P.W.map (sectionsMapLE f hV' : Γ(S, V.1) →+* Γ(S', V'.1)),
--   where sectionsMapLE := f.appLE V.1 V'.1-style composite; elliptic: map preserves IsElliptic
theorem LocalPresentation.transport_id_W …    -- the two specializations' W-fields, for rewriting
noncomputable abbrev LocalPresentation.restrict (P : LocalPresentation G V)
    (h : V'.1 ≤ V.1) : LocalPresentation G V' := P.transport (𝟙 S) (𝟙 G.E) … h'
```
**Prose (the plumbing leaf)**: the square `pullback G'.π V'.ι → pullback G.π V.ι` over
`Spec Γ(V') → Spec Γ(V)`: paste `V'.ι ≫ f = (f∣_{V'→V}) ≫ V.ι`-type factorizations with the
curve square `hsq`; `pullback G'.π V'.1.ι` is the pullback of `pullback G.π V.1.ι` along
the affine-opens map; on the model side `isPullback_projModelBaseChange` exhibits
`projModel (P.W.map …)` as the pullback of `projModel P.W` along the same `Spec` map
(transported through `V.2.isoSpec`); `e'` is the induced comparison of two pullbacks of
isomorphic diagrams (`IsPullback.isoPullback` uniqueness); `compat_π/zero` by pullback-cone
uniqueness (`hz` enters `compat_zero`). **Dischargeable**: mathlib `IsPullback` API +
`isPullback_projModelBaseChange` + `IsAffineOpen.isoSpec` naturality; sizeable but standard
plumbing; no mathematical gap. **Note**: stated with explicit `f, t, hsq, hz` (not `EllHom`)
so PART B below EllCategory-import level can use it for restriction (`f = 𝟙`), and the
EllCategory layer instantiates it with `φ.baseHom, φ.top, φ.isPullback, φ.zero_w`.

### [T-OM-B4] transport-compatibility of the comparison (naturality)
```lean
theorem LocalPresentation.transVC_transport (f t hsq hz) (P Q : LocalPresentation G V) (hV') :
    transVC (P.transport …) (Q.transport …) = (transVC P Q).map (sectionsMapLE f hV')
-- corollary: transUnit_transport (Units.map);  specialization transUnit_restrict
```
**Prose**: both sides satisfy the transported defining property: the transported
presentations' `pointedIso` is the base change of `P.pointedIso Q` along
`Spec (sectionsMapLE …)` modulo the `transport`-isos (by construction in B3), and
`projModelVCIso_map` (base-change naturality, `ModelVariableChange.lean:564`) rewrites the
base change of `projModelVCIso (transVC P Q)` as `projModelVCIso ((transVC P Q).map …)`;
`map_variableChange` gives the smul-condition; `transVC_unique` concludes.
**Dischargeable**: `projModelVCIso_map` + `map_variableChange` + B3's construction
equations; no gaps. **This leaf is the reason B3 must expose its `e'`-construction
equation as a simp/def-lemma, not hide it behind `Exists.choose`.**

### [T-OM-B5] the ω-cocycle of an atlas
```lean
noncomputable def omegaCocycle (G : EllipticCurveGeom S) : UnitCocycle S where
  ι := G.atlas.ι                       -- = S (points)
  U i := (G.atlas.U i).1
  covers := G.atlas.covers
  u i j := (Scheme.exists_unit_glue …).choose      -- glued from
    -- data V hV := transUnit ((atlas.presentation i).restrict (inf_le_left.trans' …))
    --                        ((atlas.presentation j).restrict …)  over affine V ≤ U i ⊓ U j
  u_self, u_cocycle := …               -- affine-locally by B2's laws + B4 restriction-compat,
                                       -- then A6 uniqueness / separation
```
**Prose**: for each pair `(i,j)`, the affine-local comparison units
`u^V_{ij} := transUnit (P_i|_V) (P_j|_V)` for `V ≤ U i ⊓ U j` affine form a
restriction-compatible family (B4 at `f = 𝟙`: `transUnit` of restrictions is the
restriction of `transUnit`), so A6 glues them to a unique unit `u i j` on `U i ⊓ U j`.
`u_self`: restricted to every affine it is `transUnit P P = 1` (B2), so by A6-uniqueness
(or separation) it is `1`. `u_cocycle`: restricted to every affine `V ≤ U i ⊓ U j ⊓ U k`,
`u^V_{ij} · u^V_{jk} = u^V_{ik}` (B2 `transUnit_trans`), and units glue uniquely, so the
glued sections satisfy the identity (separation on the triple overlap, using that affines
≤ the triple overlap form a basis of it). **Dischargeable**: A6 + B2 + B4; no gaps.

### [T-OM-B6] ★ the invariant differential (ω2 milestone)
```lean
noncomputable def omegaModules (G : EllipticCurveGeom S) : S.Modules :=
  (omegaCocycle G).lineBundle
noncomputable def omegaSectionsEquiv …    -- Γ(omegaModules G, V) ≃ₗ (omegaCocycle G).sections V (A3)
abbrev OmegaSection (G) := (omegaCocycle G).sections ⊤
def OmegaBasis (G : EllipticCurveGeom S) : Type u :=
  {b : (omegaCocycle G).sections ⊤ // (omegaCocycle G).IsBasis b}
-- + the A4/A5 API specialized: local triviality over every affine V inside an atlas chart;
--   the Γ(S,⊤)ˣ-action on OmegaBasis, free & transitive-on-nonempty (torsor lemmas)
```
**Prose**: assembly of PART A at `c = omegaCocycle G`. **Dischargeable**: definitional +
A3/A4/A5. **DS-register**: this is the decl the board's "DS entry is due with ω2" refers
to — on landing, register `omegaModules` as the formal ω_{E/S} with the Lean↔source match
paragraph of §1 (done in this doc; copy the pointer into the DS register with the commit).

### [T-OM-B7] ★★ base change of bases (the T-E14/engine unblock, with B6)
```lean
noncomputable def omegaCocycleCompat {X X' : EllObj R} (φ : X' ⟶ X) :
    UnitCocycle.Compat (omegaCocycle X'.curve.toEllipticCurveGeom)
      ((omegaCocycle X.curve.toEllipticCurveGeom).pullbackCocycle φ.baseHom)
    -- w (i', i) glued (A6) from transUnit ((own atlas chart i').restrict V)
    --                                     ((atlas chart i of X).transport φ.baseHom φ.top … V)
noncomputable def omegaBasisMap {X X' : EllObj R} (φ : X' ⟶ X) :
    OmegaBasis X.curve.toEllipticCurveGeom → OmegaBasis X'.curve.toEllipticCurveGeom
theorem omegaBasisMap_id … ; theorem omegaBasisMap_comp …
theorem omegaBasisMap_smul (g : Γ(S,⊤)ˣ) … -- equivariance over the units pullback
```
where `UnitCocycle.pullbackCocycle (f : Y ⟶ X) : UnitCocycle X → UnitCocycle Y` (preimage
cover + `f.appLE`-mapped units — small PART-A addendum leaf, filed under A7's ticket) and
basis-pullback `(c.pullbackCocycle f).sections (f⁻¹ V) ∋ f♯ b` componentwise.
**Prose**: a basis of `ω_{E/S}` pulls back componentwise to a basis of the pulled-back
cocycle (`f♯` of a unit is a unit — `RingHom.isUnit_map`); the `Compat` (A7) between the
pulled-back cocycle and `E'`'s own ω-cocycle has `w`-units glued from the *mixed*
comparisons "own chart vs transported chart" (B3's transport along `φ`'s square gives the
transported presentation; B2 compares; B4 gives restriction-compatibility for A6's glue;
B2's `transVC_trans` through a common third presentation gives the two `Compat` laws
affine-locally, then separation). `sectionsEquiv` (A7) transports to `OmegaBasis`.
Functoriality: for `φ ≫ ψ`, both transports satisfy the same A6-glued-unit
characterization (uniqueness of glued units + `transVC_trans` chains through the composite
transported presentation, using `transport`-functoriality `transport (f ≫ g) = transport f
∘ transport g`-shaped lemma filed in B3). **Dischargeable**: A6/A7 + B2/B3/B4; the largest
assembly leaf, but every step is uniqueness-driven; no gaps. **Consumer form**: this is
exactly what makes the Legendre/`M₁` moduli problems STATABLE as `ModuliProblem R`
functors (T-E12/T-E14): `P(X) := {(…, b) // b ∈ OmegaBasis X.curve …}` with
`P(φ) := omegaBasisMap φ` — the unblock the board calls "flips the shared engine".

### [T-OM-B8] the negation unit (ω5's identification lemma)
```lean
def negVC (W : WeierstrassCurve R) : VariableChange R := ⟨-1, 0, -W.a₁, -W.a₃⟩
theorem negVC_smul (W) : negVC W • W = W                    -- ext + ring
theorem negModelHom_eq_negVC (W) :
    negModelHom W = eqToHom (by rw [negVC_smul]) ≫ (projModelVCIso (negVC W) W).hom
theorem negVC_u (W) : (negVC W).u = -1
```
**Prose**: `negVC_smul` is coefficient algebra (mathlib `VariableChange` action formulas;
`u = -1, r = 0, s = -a₁, t = -a₃`: `a₁ ↦ -(a₁ - 2a₁) = a₁`, `a₃ ↦ -(a₃ - 2a₃) = a₃`, etc.).
`negModelHom_eq_negVC`: both sides are `Proj.map` of explicit graded substitutions
(`negVec` vs `vcMvSubst (negVC W)` — compare: `negVec` sends `Y ↦ -Y - a₁X - a₃Z`, and
`vcMvSubst ⟨-1,0,-a₁,-a₃⟩` sends `Y ↦ u³Y + su²X + tZ`-pattern `= -Y - a₁X - a₃Z` ✓,
`X ↦ u²X + rZ = X` ✓, `Z ↦ Z` ✓); equality via `Proj_map_congr` + `HEq` transport along
`negVC_smul` (the `projMap_transport_heq` idiom of `projModelVCIso_one/_mul`).
**Dischargeable**: `GroupLawConstruction.negModelHom` unfolding + the transport idiom;
mechanical. **Source**: Silverman III.1 (the inversion `(x,y) ↦ (x, -y - a₁x - a₃)`);
KM 4.6.2's `{±1}` = this automorphism's action `ω ↦ -ω`, formally: its `transUnit` is
`(negVC).u = -1`, so through B7's functoriality the inversion `EllHom` scales every
ω-basis by `-1`. The full "inversion-EllHom acts by `-1` on `OmegaBasis`" statement chains
B8 through B7 and the chart-wise description of the inversion morphism (`invOver`,
`GroupLawDescent`); that assembly is **deliberately deferred to T-E14's own decomposition**
(it needs `invOver`-chart lemmas internal to the descent layer; T-E14 spawns it as a leaf —
recorded on the board under T-E14's `Depends on`).

## 5. Order of work & milestones

Dependency order: A1 → A2 → A3 → A4 → A5; A6 independent (after A1's notation only);
A7 after A1–A6; B1 → B2 → B3 → B4 → B5 (needs A6) → B6 ★ (needs A1–A5) →
B7 ★★ (needs A7 + B2–B6) ; B8 independent (ModelVariableChange level only); A8 last
(risk-flagged, optional for the stream).

Reports to the board (charter): the R1 decompose ★ (this document + skeleton),
B6 = ω2 glued invertible sheaf ★, B7(+B6+B8) = T-E14 unblock ★★.

## 6. Generality decisions

- PART A over `Scheme.{u}` with `ι : Type u` — matches every consumer; LocallyRingedSpace
  generalization deferred to mathlib upstreaming (`/mathlibable` candidate after landing).
- `LocalPresentation` over `S.affineOpens` — forced by 1b's ring-level statement.
- B3's transport with explicit square data (not `EllHom`) — so the restriction
  specialization needs no EllCategory import; EllObj-level wrappers live with B7.
- No `Ω¹`, no conormal, no `H¹` machinery anywhere — everything is uniqueness-driven
  gluing of the comparison units. The object is pinned up to canonical isomorphism by its
  chart trivializations (A4) + transitions (B5), which is exactly how every source
  (KM 2.2, GME 2.2, Silverman III.1) computes with `ω_{E/S}`.
