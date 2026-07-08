# Worker decomposition — [T-G3d-infra] Piece 3: the coequalizer scheme `E/G`

*p0, 2026-07-08. Piece 3 of `decomposition-g3d-infra.md` — the one genuinely hard, scheme-theoretic
piece. Pieces 1 (interface), 2 (the `IsInvariant ⟺ coequalizer` bridge), 4 (factored map) are LANDED
and axiom-clean. This is the construction of the coequalizer scheme of `act, pr_E : G ×_S E ⇉ E`
(= `E/G`), after which all three interface pins read off mechanically through
`isInvariant_iff_coequalizes`.*

## What "build the scheme" buys, exactly
The bridge already did the hard categorical work. Concretely, once we have a scheme `Q`, a map
`π : E ⟶ Q`, and a proof `hπ : G.IsInvariant π` **that is universal** (every `G`-invariant `f` factors
uniquely through `π`), the pins are:
- `quotient := Q`, `quotientπ := π`, `quotientS := (the induced Q ⟶ S)`.
- `quotientπ_isInvariant := hπ` (directly, or `IsInvariant.of_coequalizes` from `π` coequalizing).
- `quotient_lift := the universal factoring` (its hypothesis `G.IsInvariant f` ⟹ `f` coequalizes via
  `IsInvariant.coequalizes` ⟹ factors).
- `quotientπ_over` from `quotientS`.

So the deliverable is precisely: **a universal coequalizer `π : E ⟶ Q` of `act, pr_E`** (with `Q ⟶ S`).

## Route decision (pending the mathlib/project recon)
- **If mathlib has coequalizers of schemes for this shape, or a finite-flat-groupoid quotient**: use
  it directly — `Q := coequalizer act pr_E` (or the groupoid-quotient API) and read off the pins.
  Cheapest by far. (Recon Q1/Q2.)
- **If the project's `ForMathlib/SchemeQuotient.lean` glue-data generalises**: adapt it. It is written
  for a CONSTANT `[Group G]` action; the group-SCHEME case needs the local piece to be the comodule
  coinvariants (below), but the glue skeleton may be reusable verbatim. (Recon Q3.)
- **Else, from scratch (route 3a)** — the affine-coinvariants-glue stack:
  - **3a-i (co-action `ρ`)**: the translation co-action at the ring/sheaf level, the dual of
    `translationAction`. Affine-locally on a `G`-stable `Spec B ⊆ E`, `ρ : B → B ⊗_R A` (`A = O_G`),
    `ρ = act^# ` under `O(G ×_S Spec B) ≅ B ⊗_R A` (`G` finite ⟹ affine over the base).
  - **3a-ii (coinvariants)**: `B^{coG} := eq(ρ, b ↦ b ⊗ 1)` as an `R`-subalgebra (mathlib coalgebra
    coinvariants if available — recon Q4 — else built here), and `Spec B ⟶ Spec B^{coG}` with its
    universal property (comodule analogue of `AffineQuotient`'s `existsUnique_invariantsπ_lift`).
  - **3a-iii (G-stable affine cover)**: `E` quasi-projective over `S` ⟹ every finite `G`-orbit lies
    in an affine open ⟹ a `G`-stable affine cover exists. (Real theorem; may itself decompose.)
  - **3a-iv (glue)**: glue the `Spec B^{coG}` on p2's `SchemeQuotient` glue-data pattern; `π`, `Q ⟶ S`,
    universality. p2-stack-scale.
- **fppf route (3b)** is GATED: representability of the fppf coequalizer needs SGA-III / ample inputs
  (cf. the board's T-E10 gate) that are not currently available — do not take unless those land.

## Off-critical-path but needed for [T-G3d-Niso] (separate ticket): freeness
`actPair = ⟨act, pr_E⟩ : G ×_S E ⟶ E ×_S E` is a **monomorphism** (the action is free). Route:
`actPair = (ιOver ⊗ 𝟙) ≫ shear` where `shear = lift μ pr_E : E ×_S E ⟶ E ×_S E`, `(a,b) ↦ (a+b, b)`;
`shear` is a split mono (retraction `(u,v) ↦ (u-v, v)`, needs the group-object cancellation
`(a+b)-b = a`); `ιOver` mono from `G.closedImmersion` (`IsClosedImmersion ⟹ Mono`); `f ⊗ 𝟙` mono from
`f` mono (cartesian). Feeds the degree count `deg[N] = N² = rank E[N]` in `E/E[N] ≅ E`. Route-
independent of the construction, but only meaningful once `Q` exists — so sequence it AFTER a route
for `Q` is chosen.

## Status
Recon dispatched (mathlib coequalizers / finite-flat-groupoid quotients / `AffineQuotient` reusability
/ comodule coinvariants / closed-immersion mono). Route chosen on its return; then decompose the
chosen route into leaf tickets and build. Route 3a is the fallback and is p2-stack-scale (multi-
session); 3b is gated; a mathlib/`SchemeQuotient` reuse would collapse most of it.
