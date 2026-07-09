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

### Route (b) — cohomology-free rigidity via `f_*O_X = O_S` (MODERN, avoids Krull)
Re-prove `isOpen_germMap_ideal_eq_bot`'s conclusion (openness of the constancy locus) over an
arbitrary base using the **pushforward-connectedness** `f_*O_X = O_S`, which the project ALREADY has
arbitrary-base with **no cohomology** (`locallyWeierstrass_pushforward_O_eq_O`, T-W7.0i·i5; GIT
p.115 "one knows f_*O_X = O_S"). The modern rigidity lemma (constancy propagates because
`h : X → Z` factors through `f_*O_X = O_S`) does not need Krull.
- **Blocker:** the *openness/closedness* of the constancy locus over an arbitrary base still needs
  a semicontinuity input — classically cohomology-and-base-change (proper base change). That is a
  smaller mathlib gap than (a), and the project's explicit Weierstrass `f_*O = O` may let a
  section-level (cohomology-free) openness argument replace it. **Needs the GIT p.114–115 rigidity
  proof read to confirm the cohomology-free openness step is real, not invented.**
- **Effort:** medium (re-prove the rigidity chain's openness step via pushforward, reusing the
  existing `exists_factor_of_connected` skeleton with the Krull step swapped out).
- **Source:** Mumford GIT §6 (Cor 6.4 + the rigidity lemma), read the openness step verbatim.

### Route (a) — formalize EGA IV §8 spreading-out (LAST RESORT)
Reduce arbitrary `S` to noetherian by spreading out: every scheme is a cofiltered limit of
finite-type-ℤ (noetherian) schemes, and finite-presentation properties (here: the group-hom
identity of two morphisms) descend to a finite level, where the noetherian rigidity applies.
- **Blocker:** EGA IV §8 spreading-out is **absent from mathlib** and is a MAJOR contribution
  (limits of schemes + finite-presentation descent of morphisms/properties). Months-scale.
- **Effort:** very large (mathlib-scale). Only pursue if (c) and (b) both genuinely fail.
- **Source:** EGA IV §8 (Grothendieck) / Stacks Project "Limits of Schemes" (Tag 01YT ff.).

## Recommendation

1. **Investigate route (c) first** — it is cheapest and avoids every mathlib gap, and it is the
   natural landing spot given T-W7.1b already gave `pointedIso_exists_variableChange` +
   `projModelBaseChange`. It is **gated on c5β's group-law construction (0c-ii/`mulModelHom`)**
   landing base-change-natural. Do NOT start T-W7.8 before that lands; when it does, route (c) is
   likely a short corollary. **This aligns T-W7.8 behind the W7 endgame, not spreading-out.**
2. If route (c) is structurally blocked (the abstract group object cannot be identified with the
   explicit law), fall to **route (b)** — re-prove rigidity's openness step cohomology-free via the
   existing `f_*O_X = O_S`; read GIT §6 to confirm.
3. **Route (a) is the last resort** and should be its own multi-month mathlib project, not part of
   the ModularCurves endgame.

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
