# Development Plan: T-W7.8 — arbitrary-base canonicity (un-park `pullSection_add` + the T-E4 family)

*Strategic plan (`/develop`). This is a research-scale, blocked-on-mathlib gap; the leaf-level
ticket board is deliberately deferred until the route is chosen, because each route's
decomposition is faithful to a DIFFERENT source (source-faithfulness rule). The one deciding
question (§Deciding question) picks the route; then the chosen route's Phase-1e runs.*

## Goal (the actual crux, verified against the code)

Un-park `EllHom.pullSection_add` (`Representability.lean:207`) and the Γ₁/Γ(N) functor-law
membership sorries — which clears the `sorryAx` inheritance in YFULL AFF/FIN, GH1, and the naive
functor maps. **But `pullSection_add` is not itself the gap.** The noetherian version
(`pullSection_add_of_isLocallyNoetherian`, `PullSectionAdd.lean:169`) already reduces it, via
`transportSection_add` (:102), to exactly ONE noetherian-only ingredient:

> **`isMonHom_of_one_comp_eq'`** (Rigidity.lean, = GIT Cor 6.4 = T-W7.7): the pointed comparison
> iso `curveIsoPullback : X.curve.E ≅ pullback Y.curve.π f.baseHom` between the two independent
> group structures is automatically a **group homomorphism** — currently `[IsLocallyNoetherian]`.

**So T-W7.8 = removing `[IsLocallyNoetherian]` from the rigidity/canonicity theorem.** Everything
above it (`pullSection_add`, `pullSection_zsmul`, the functor-map memberships, the sorryAx
inheritance) is a mechanical wiring once T-W7.8 lands — *those are not the work*; the rigidity
upgrade is.

## Why the current proof is noetherian (verified, not assumed)

The rigidity chain — `rigidity` (:929) → `rigidity_of_forall_component` (:955) →
`exists_factor_of_connected` (:906) → `exists_factor_of_forall_component` (:815) →
`exists_open_factor_of_fibre_subset` (:702) → `germ_ker_mem_pow_of_fibre_subset` (:534) →
`isOpen_germMap_ideal_eq_bot` (:391) — bottoms out on a **germ-power / Krull-intersection**
argument: the ideal cutting the constancy locus lies in every power `mⁿ` of the maximal ideal,
hence is `0` because `Γ(X,U)` is a **noetherian** local ring (Krull's intersection theorem). This
is genuinely noetherian — it is the classical rigidity-lemma proof, and Krull needs noetherian.

## Three routes (honest mathlib-gap analysis)

### Route (c) — EXPLICIT Weierstrass, bypass rigidity entirely (INVESTIGATE FIRST)
If the two group structures being compared are (base-change-compatibly) the **explicit Weierstrass
addition** — X.curve's law = the f-pullback of Y.curve's law, both the same chord-tangent
morphisms — then `curveIsoPullback` is a hom **by construction** (base change of a hom is a hom),
with NO rigidity, NO noetherian, NO mathlib gap.
- **Blocker to confirm:** the current setup uses the *abstract* rigidity (`rigidity` operates on an
  abstract proper-flat-O-connected group object `MonObj … .asOver`), so today's proof does NOT take
  this route. Viability hinges on whether the project's **explicit** group law
  (`GroupLawConstruction`: `mulModelHom` etc.) is (i) landed and (ii) base-change-natural
  (`map_mulModelHom`-style). **`mulModelHom` is currently c5β's sorried WIP** (0c-ii), so route (c)
  is gated on the group-law construction landing — but if it lands base-change-natural (it should,
  by the same `projModelBaseChange`/`isPullback_projModelBaseChange` machinery T-W7.1b used), route
  (c) makes T-W7.8 a short corollary and **avoids EGA IV §8 entirely**.
- **Effort:** small once c5β's group law lands (a base-change-naturality lemma + a corollary).
- **Source:** the project's own explicit construction; no external heavy source.

### Route (b) — cohomology-free rigidity via `f_*O_X = O_S` — ❌ REFUTED (source-read, GIT §6)
**Investigated and rejected (2026-07-09, read `mumford-GIT.pdf` pp.114–116).** The "cohomology-free
elementary openness" idea was an INVENTION, not Mumford's proof (rule-4 catch). Verbatim from GIT:
- Ch. 6 opening (p.114): *"For the sake of simplicity, all pre-schemes in this chapter will be
  assumed to be locally noetherian."* — the source is noetherian by assumption.
- **Prop 6.1 (rigidity lemma) proof is genuinely noetherian.** Case 2 (verbatim, p.116): *"if Z
  contains `p⁻¹(t)` set-theoretically, for any `t∈S`, then for all artin subschemes `T⊂S`
  concentrated at `t`, `Z` contains `p⁻¹(T)` as a subscheme. But this implies `Z` actually contains
  some open neighborhood `U` of `p⁻¹(t)`."* — the "artin-subschemes ⟹ open neighborhood" step **is**
  Krull's intersection (`⋂ mⁿ = 0` in a noetherian local ring); it is exactly the current code's
  `germ_ker_mem_pow_of_fibre_subset`. The current proof is FAITHFUL to Mumford, not a heavy detour.
- Case 3 (proper, p.117): *"after a faithfully flat base extension `S'/S` … we can assume `X'/S'`
  has a section. Then by case 2) … `η'` must also descend to a morphism `η : S → Y` (cf. **SGA 8,
  Th. 5.2**)."* — the proper case reduces to case 2 (still noetherian) + **SGA 8 descent**.
- My "affine-nbhd + proper-closed-map" argument only factors `f` **locally near `s₀`** (fixed affine
  `V ∋ f(X_{s₀})`); it does NOT globalize — globalization IS the artin/Krull openness or SGA 8.
  Incomplete, hence rejected.

**Conclusion:** arbitrary-base rigidity needs either the artin/Krull openness (noetherian, route (a)
via SGA 8 spreading-out) OR cohomology-and-base-change (proper base change) for the openness —
**both are genuine mathlib gaps.** There is no cohomology-free elementary route. Route (b) collapses
into route (a)'s mathlib gap.

### Route (a) — formalize EGA IV §8 spreading-out (LAST RESORT)
Reduce arbitrary `S` to noetherian by spreading out: every scheme is a cofiltered limit of
finite-type-ℤ (noetherian) schemes, and finite-presentation properties (here: the group-hom
identity of two morphisms) descend to a finite level, where the noetherian rigidity applies.
- **Blocker:** EGA IV §8 spreading-out is **absent from mathlib** and is a MAJOR contribution
  (limits of schemes + finite-presentation descent of morphisms/properties). Months-scale.
- **Effort:** very large (mathlib-scale). Only pursue if (c) and (b) both genuinely fail.
- **Source:** EGA IV §8 (Grothendieck) / Stacks Project "Limits of Schemes" (Tag 01YT ff.).

## Recommendation (UPDATED after route (b) refuted by GIT §6)

With route (b) refuted, only two routes survive, and one is a months-scale mathlib project:

1. **Route (c) is now the ONLY tractable path — pursue it, gated on c5β's endgame.** It avoids the
   rigidity theorem entirely (the explicit Weierstrass law, base-change-natural, makes the
   comparison iso a hom by construction), so it sidesteps the SGA 8 / cohomology-and-base-change gap
   that BOTH the source (Mumford Prop 6.1 case 3) and route (a) require. It is **gated on c5β's
   `mulModelHom` (0c-ii) landing base-change-natural**. Do NOT attempt T-W7.8 standalone; wait for
   the endgame, then confirm route (c) via the Deciding question. **This vindicates the owner's
   2026-07-08 parking decision — waiting for the endgame is correct, not a punt.**
2. **Route (a) (SGA 8 / EGA IV §8 spreading-out) is the genuine fallback if route (c) is
   structurally blocked** — and it is a self-contained, multi-month mathlib contribution (limits of
   schemes + fppf descent of morphisms per Mumford's own SGA 8 Th. 5.2 citation), NOT part of the
   ModularCurves endgame. It should be scoped as an independent upstream project if ever needed.

**Net:** the source-read collapsed three routes to one tractable one (route (c), endgame-gated) plus
a months-scale mathlib fallback (route (a)). There is no quick win here; T-W7.8 correctly waits
behind the W7 endgame.

## Deciding question (answer this before the leaf-level ticket board)

**Is the ModularCurves curve group law that `isMonHom_of_one_comp_eq'` compares (i) the explicit
`GroupLawConstruction` Weierstrass law, and (ii) base-change-natural?** If YES → route (c), T-W7.8
is a corollary of the W7 endgame; write that ticket board. If the compared law is irreducibly
abstract → route (b); read GIT §6 and write that board. This is a design/code-reading question +
one source read, not a proof — cheap to resolve, and it picks the route so the decomposition is
faithful to the right source.

## Scope honesty

T-W7.8 is correctly "blocked-on-mathlib" *only for route (a)*. Routes (c)/(b) are NOT blocked on
mathlib — (c) is blocked on the in-fleet W7 endgame (c5β), (b) on a bounded cohomology-free
re-proof. The owner's 2026-07-08 parking decision (keep arbitrary bases) is consistent with
waiting for route (c) to fall out of the endgame. **The single highest-value action is to confirm
route (c) once `mulModelHom` lands — likely turning a "months of spreading-out" into "a corollary."**

## UPDATE 2026-07-09 — route (a) is TRACTABLE (owner-directed build; my "months-scale" was STALE)

Owner (v-fork) directed **build route (a)** now. Two ground-truth surveys (mathlib state +
Stacks chain) overturn this plan's central "months-scale / absent from mathlib" claim — it
**pre-dated the daily bump** that landed `Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean`
(inverse limits of schemes w/ affine transition maps, "following EGA IV 8 / Stacks 01YT").

**Crux pinned (code-verified):** the noetherian hypothesis is removable from
`isMonHom_of_one_comp_eq'` (`Rigidity.lean:1443`); its conclusion is an **equality of two
`S`-morphisms `A ⊗ A ⟶ G` into a separated target** — the most spreading-out-friendly shape.
The whole `rigidity` chain's only noetherian use is Krull (`iInf_pow_eq_bot`); everything else
is Hom-group algebra.

**Reduction (skeleton = `EllipticCurve/RigiditySpreadingOut.lean`, GREEN, sorry-only):**
target `isMonHom_of_one_comp_eq'_of_finitePresentation` (drop `[IsLocallyNoetherian S]`, add
`[LocallyOfFinitePresentation A.hom] [LocallyOfFinitePresentation G.hom]`). Leaves: **L1**
affine-local reduction (equality is local on `S`; `Gₐ ↪ G` open immersion — sidesteps the hard
qcqs Stacks 01ZA) → **L2** base-change the GrpObj config (mathlib `Over.pullback` monoidal +
project `Over.grpObjMkPullbackSnd`) → **L3** affine approx `Spec R = lim Spec Rⱼ`, `Rⱼ` finite-
type-ℤ (`Spec` preserves limits + `Subalgebra.iSupLift`) → **L4a** descend objects/morphisms
(mathlib `exists_hom_hom_comp_eq_comp` `@[stacks 01ZC]`, `exists_π_app_comp_eq…`) → **L4c**
descend PROPERTIES (proper/flat/separated/lfp/O-conn; Stacks 081D) → **L5** apply noetherian
`isMonHom` at stage → **L6** base-change equality back (free).

**The one mathlib-absent piece = L4c (property-descent along limits, Stacks 081D/081E/01ZP/01ZQ).**
Genuinely-reusable upstream infra; **labor, not a research unknown** (the limit API + ring-colimit
foundation support it). Net revised scope: **weeks-scale, not months**; the affine-local reduction
is what shrinks it (no Thomason–Trobaugh qcqs approximation needed). Leaf board = tasks #9–#14.
