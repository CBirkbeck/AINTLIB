# /develop --decompose — the relative Picard functor `Pic_{E/S}` (GME §2.2.2, (2.16) stream)

**Date**: 2026-07-12 · **Worker**: fable-PIC0 · **Charter**: CHARTER-PIC-3 stream (2)
(v10.141), banked-queue item 3. **Skeleton**: `ModularCurves/Picard/RelativePic.lean`
(compiles, 8 sorries). **Prereq state**: [PIC-P2-CMP] complete (v10.158) — `Pic X`
CommGroup + `Pic.map`/`map_id`/`map_comp` + GME 2.17 both directions, all sorry-free.

## Ecosystem re-check (standing watch duty, run first)

- mathlib `RingTheory/PicardGroup.lean` (Junyan Xu, 2025): **ring-level** `CommRing.Pic`
  only. Its module docstring TODO explicitly lists "Connect to invertible sheaves on
  `Spec R`" as NOT done. No scheme-level Pic, no relative Pic, no rigidified bundles:
  `grep -rln "PicardGroup|relative Picard|Pic⁰|rigidified" Mathlib/AlgebraicGeometry/`
  is EMPTY. No collision; our `Scheme.Pic` remains the only scheme-level Picard group in
  the ecosystem. Re-checked 2026-07-12.

## Source (verbatim, GME = Hida, *Geometric Modular Forms and Elliptic Curves*, 2001)

**[Q1] The functors (p. 108, §2.2.2, proof of Theorem 2.2.1):**
> "We write E_T for E ×_S T and Pic(E_T) for the group of isomorphism classes of all
> invertible sheaves on E_T. Then we consider the following contravariant functors
> Pic_{E/S}, Pic^ν : SCH_{/S} → SETS for integers ν:
> Pic_{E/S}(T) = Pic(E ×_S T)/f_T^* Pic(T)   for f_T : E ×_S T → T,
> Pic^ν_{E/S}(T) = [ L ∈ Pic_{E/S}(E_T) | deg(L(t)) = ν for t ∈ T ], where [ ] = { }/≈,
> L ≈ L' ⟺ L ≅ L' ⊗ f_T^*(L₀) for an invertible sheaf L₀ on S, t runs over all
> geometric points of T, and L(t) = L|_{E_t} for the fiber E_t over t."

**[Q2] Functoriality (p. 108):**
> "If g : T' → T is an S-morphism, we have g_E = 1_E ×_S g : E'_T → E_T. This induces
> Pic^ν(g)(L) = g_E^*(L)."

**[Q3] The group structure (p. 108 bottom):**
> "Since Pic⁰ is a group functor with the identity O_E under the multiplication:
> L · L' = L ⊗ L', if (2.16) is true, the theorem is proven except for the uniqueness
> of the group structure."

**[Q4] The kernel model (p. 109, proof of (2.17)):**
> "Since we have the 0-section 0 : S ↪ E, we have a group homomorphism
> 0* : Pic(E) → Pic(S) for which f* is a section. Thus Pic(E) = Ker(0*) ⊕ Im(f*) and
> therefore Pic_{E/S} is actually a subfunctor of Pic_{/E}."

**[Q5] (2.16) itself (p. 108):**
> "We want to show E ≅ Pic¹ ≅ Pic⁰ via P ↦ I(P)⁻¹ ↦ I(P)⁻¹ ⊗ I(0). (2.16)"

**[Q6] The deep clause (p. 109, surjectivity of ι):**
> "We may assume that S = Spec(A). Since L ∈ Pic¹(S) is fiber by fiber of degree 1, as
> already seen (at the end of Subsection 2.2.1), f_*L is locally free and
> rank_{O_S}(f_*L) = 1. […] Then we have an exact sequence: 0 → O_E → L → (L/O_E) → 0,
> which yields another exact sequence: 0 → f_*O_E → f_*L → f_*(L/O_E) → R¹f_*O_E ≅ O_S
> → 0. […] This shows that (L, ℓ) is an effective Cartier divisor relative to S […]
> Hence, there is a section P : S ↪ E such that L = I(P)⁻¹."

## Layering decision (source-faithful cut)

The (2.16) statement [Q5] has three layers with sharply different formalization depth:

- **L-A (functor layer)** — the objects in [Q1]–[Q4]: `Pic_{E/S}` as a contravariant
  group functor. Needs ONLY the landed `Pic`/`Pic.map` machinery + scheme pullbacks.
  **This is what the skeleton covers.** Per [Q4], we take the KERNEL model as the
  definition (`picRel := (Pic.map z_T).ker`) — this is Hida's own working model for
  locality, and it dodges quotient-group transport in every downstream use. The
  displayed quotient of [Q1] is recorded as a comparison iso
  (`nonempty_picRel_mulEquiv_quotient`), not the definition.
- **L-B (degree layer)** — `Pic^ν` in [Q1] needs `deg(L(t))` on geometric fibres:
  fibre restriction of invertible sheaves + degree on curves over fields. The old
  scoping ticket [T-PIC-DEG0] (board v≤10.15) already flagged the HasseWeil
  divisor/degree anchor audit. DEFERRED to its own /develop pass; nothing in L-A
  depends on it.
- **L-C (Abel, (2.16) proper)** — `E ≅ Pic¹ ≅ Pic⁰` [Q5] requires the relative
  cohomology run in [Q6]: `R¹f_*`, relative Riemann–Roch (GME Cor 2.1.6/2.1.7),
  semicontinuity, and the effective-relative-Cartier-divisor extraction (GME
  pp. 106–107). The arc pin (board, stage-P2 note) explicitly excludes the
  surjectivity clause: "Semicontinuity ([Mum] Cor 1) and Hida's surjectivity clause:
  explicitly out of pin, not cut". DEFERRED; L-C is a future arc gated on a relative
  cohomology library.

## Decomposition tree (L-A; skeleton = `RelativePic.lean`)

Setting: `p : E ⟶ S`, `z : S ⟶ E`, `hz : z ≫ p = 𝟙 S` (any retraction pair — the
elliptic-curve structure is NOT needed for L-A; generality per source: [Q4] uses only
the 0-section).

1. **`baseChangeZero`** (def, done in skeleton): `z_T := pullback.lift (t ≫ z) (𝟙 T)`.
   Source: [Q1]'s `f_T` + [Q4]'s `0`-section, base-changed. Discharge: mathlib
   `pullback.lift`. *Attacks*: (a) wrong-slot lift (`fst` vs `snd` conventions) — the
   lift condition `(t ≫ z) ≫ p = 𝟙 T ≫ t` fixes the slots, compiles; (b) does the
   section base-change exist without flatness? — yes, `pullback.lift` is categorical;
   (c) mathlib might already have named base-change-of-section — searched
   `Mathlib/AlgebraicGeometry/Pullbacks.lean` (`pullbackRestrictIsoRestrict`, etc.):
   no named section-base-change; local def justified.
2. **`baseChangeZero_snd`**: `z_T ≫ f_T = 𝟙`. Discharge: `pullback.lift_snd`.
   *Attacks*: definitional-unfold only; no content to be wrong.
3. **`picRel`** (def, done): `(Pic.map z_T).ker`. Source: [Q4] verbatim. *Attacks*:
   (a) is `Ker(0*)` really isomorphic to Hida's quotient? — [Q4] says the splitting
   holds because "f* is a section" of 0*, which is leaf 4's content; (b) kernel of a
   MonoidHom on `Pic` needs `Pic` to be a group — landed CommGroup instance; (c) the
   0* here is at level `T`, not `S` — matches [Q1]'s "Replacing S by T" (p. 109 top).
4. **`nonempty_picRel_mulEquiv_quotient`**: `Pic(E_T)/f_T^*Pic(T) ≃* Ker(z_T^*)`.
   Source: [Q4] ("Pic(E) = Ker(0*) ⊕ Im(f*)"). Proof sketch: `z_T ≫ f_T = 𝟙` gives
   `(Pic.map z_T).comp (Pic.map f_T) = id` (via `Pic.map_comp` + `Pic.map_id`); for a
   split surjection of abelian groups, `G ⧸ range(section) ≃* ker(retraction)` by
   `x ↦ x * (f_T^* (z_T^* x))⁻¹`. Discharge plan: hand lemma (~15 lines) or mathlib
   splitting API. *Attacks*: (a) direction of the retraction — `Pic.map` is
   contravariant, so `z_T^* ∘ f_T^* = (z_T ≫ f_T)^* = id` — checked against
   `Pic.map_comp`'s composition order `Pic.map (g ≫ f) = (Pic.map g).comp (Pic.map f)`;
   (b) noncommutative pitfalls — none, `Pic` is CommGroup; (c) is the quotient the
   right ⁠`≈` from [Q1]? — [Q1] quotients by `L ≅ L' ⊗ f_T^*(L₀)`, i.e. exactly by
   `range (Pic.map f_T)` in `Pic(E_T)`; match verified against the displayed formula.
5. **`baseChangeMap`** (def, done): `g_E := pullback.map … (𝟙 E) g (𝟙 S)`. Source:
   [Q2] "g_E = 1_E ×_S g". Discharge: mathlib `pullback.map`. *Attacks*: slot
   conventions (compiles with the `hg`-square); identity-components per [Q2].
6. **`baseChangeZero_baseChangeMap`**: `z_{T'} ≫ g_E = g ≫ z_T`. Needed for leaf 7.
   Discharge: `pullback.hom_ext` + `lift_fst/snd/map_fst/map_snd` simp. *Attacks*:
   (a) this is the ONLY place functoriality of the section enters — if false, the
   kernel is not preserved; verified by components: fst: `t' ≫ z = g ≫ t ≫ z` (uses
   `hg`), snd: `𝟙 ≫ g = g ≫ 𝟙`; (b) both sides target `pullback p t` — typechecks in
   skeleton.
7. **`pic_map_baseChangeMap_mem`**: `g_E^*` preserves `Ker(z^*)`. Source: [Q2] (the
   induced map). Proof: `z_{T'}^*(g_E^* L) = (z_{T'} ≫ g_E)^* L = (g ≫ z_T)^* L =
   g^*(z_T^* L) = g^* 1 = 1` via `Pic.map_comp` + leaf 6 + `map_one`. *Attacks*:
   (a) needs `Pic.map` monoid-hom (map_one) — it is a `→*`; (b) order of comp in
   `Pic.map_comp` again — same check as leaf 4; (c) nothing else can fail: two
   rewrites and a `map_one`.
8. **`baseChangeMap_id` / `baseChangeMap_comp`**: `pullback.map`-functoriality.
   Discharge: `pullback.hom_ext` + simp (mathlib has `pullback.map_id/map_comp`-shaped
   simp lemmas; if names drifted, ext+simp closes). *Attacks*: proof-irrelevant
   `hg`-arguments make the statements typecheck (the `(by rw …)`-argument in `_comp`'s
   statement is definitionally irrelevant — Prop-proof).
9. **`picRelFunctor`** (def, data done; `map_id`/`map_comp` sorried): obj/map as in
   skeleton via `codRestrict`. Source: [Q1] ("contravariant functors … SCH_{/S} →
   SETS") upgraded to `CommGrpCat` per [Q3]. Discharge of the laws: `Subtype.ext` +
   leaves 8 + `Pic.map_id/comp` congruence. *Attacks*: (a) `(Over S)ᵒᵖ ⥤ CommGrpCat`
   vs Hida's `SCH_{/S} → SETS`: we bundle the group structure — strictly more, and
   [Q3] justifies it; (b) universe: `Pic` lives in `Type (u+1)` (units of the module
   skeleton) — functor targets `CommGrpCat.{u+1}`; compiles; (c) `Over.w g.unop`
   supplies the `hg`-square exactly.

## Provability audit

Every leaf discharges from: mathlib `pullback.lift/map/hom_ext` + landed
`Pic`/`Pic.map`/`map_id`/`map_comp` + one ~15-line abelian splitting lemma (leaf 4).
No new mathematical gaps. No leaf requires elliptic-curve hypotheses — the entire L-A
layer works for any retraction pair `(p, z, hz)`, which is both more general and
faithful to [Q4]'s mechanism.

## Confidence gate

Skeleton compiles sorries-only against the current tree ✓. Every leaf carries a [Q]-tag
✓. No leaf invents a route absent from the source: the kernel model IS Hida's ([Q4]),
the comparison keeps the displayed definition honest ✓. L-B/L-C deferred with quotes
and pin citations, not silently dropped ✓.

## Next steps

1. Work leaves 2, 6, 8 (mechanical `pullback` API), then 7, then 4 (splitting lemma),
   then 9's laws. Estimated: one focused session.
2. Then: L-B scoping pass ([T-PIC-DEG0] audit) as its own `/develop --decompose`.
3. L-C stays pinned out until a relative-cohomology arc exists.
