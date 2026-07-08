# Worker decomposition — [T-G3d-infra]: the quotient `E/G` by a finite locally free subgroup scheme

*p0, 2026-07-08 (coordinator v10.27→ dispatch). Build the quotient-by-finite-locally-free-subgroup-
scheme layer on p2's `ForMathlib/SchemeQuotient.lean` glue-data PATTERN (read-only; never touch p2's
live-sentinel files). Ship the opaque interface in the same increment (v10.24(b)); the construction
half alone is a full deliverable; the `[N]`-iso half decomposes+boards if it walls on degree facts.
Three consumers: T-G3d's `E/E[N] ≅ E`, review-Q8 N-Isog, the `Γ₀` path.*

## Input / output
- **Input**: `G : FiniteLocallyFreeSubgroup E` (p2 `GroupScheme/Subgroup.lean`) — a scheme `G.G`,
  closed immersion `ι : G.G ⟶ E.E`, with `finite`/`flat`/`lfp` over `S` as **given fields** and the
  functor-of-points `subgroup` field. **NOT gated** on the `E[N]`-finite-étale linchpin: the
  construction takes `finite`/`flat` as input; only the *torsion instance* `torsionSubgroup N` gates
  them on `BB-QF`/`BB-FLAT` (P3b3 + D2's lanes).
- **Output**: `E/G` + quotient isogeny + universal property = **Piece 1, LANDED** in
  `GroupScheme/SubgroupQuotient.lean` (interface: `IsInvariant`, `quotient`/`quotientS`/`quotientπ`
  DS-data, pins `quotientπ_over`/`quotientπ_isInvariant`/`quotient_lift`, PROVEN `IsInvariant.comp`
  and `quotientπ_hom_ext`).

## Pieces

1. **[DONE] Interface** — the categorical-quotient universal property as the opaque interface.
   Consumers touch only this. `quotientπ_hom_ext` is proved from `quotient_lift` +
   `quotientπ_isInvariant`. The three DS-data + three pins are the deferred construction.

2. **Affine co-invariant quotient** (the local block). For an affine `Spec B ⊆ E` translation-stable
   under `G`, `(Spec B)/G = Spec(B^{coG})` where `B^{coG} = eq(coaction, b ↦ b⊗1)` are the invariants
   of the **translation co-action** `ρ : B → B ⊗_{O_S} O_G`. Mirror p2's `ForMathlib/AffineQuotient.lean`
   (which does `Spec Bᴳ` for a constant *group* `[Finite G]`) but for a **comodule**.
   - The translation co-action `ρ` is **self-buildable** (do NOT wait on p2's Hopf `subgroupComul`,
     which is the coalgebra `O_G → O_G ⊗ O_G`, a different map): `ρ` is dual to the action
     `act : G ×_S E → E`, `(g,x) ↦ ι(g) + x`, i.e. `(ι ×_S 𝟙) ≫ addE` where `addE = (μ[E.asOver]).left`.
   - Universal property of the affine block: a `ρ`-invariant `B → C` factors uniquely through `B^{coG}`
     (the comodule analogue of `existsUnique_invariantsπ_lift`). This is the real construction work.

3. **Glue** — glue the local affine co-invariant quotients over a `G`-stable affine cover of `E`,
   producing `quotient`/`quotientπ` and discharging the pins. Mirror p2's `SchemeQuotient.lean`
   `quotientGlueData`/`quotient`/`quotientπ_hom_ext` — the same glue-data skeleton, with the local
   piece supplied by Piece 2. `quotientS` from the induced map to `S`. This is p2-stack-scale
   (~the size of their `SchemeQuotient`), a multi-session build.

4. **`[N]`-iso consumer** (T-G3d) — `E/E[N] ≅ E` via `[N]`. `[N] : E ⟶ E` is `E[N]`-invariant
   (`[N](x+t) = [N]x + [N]t = [N]x` for `t ∈ E[N]`, since `[N]t = 0` and `mulByHom` is additive on
   points), so `quotient_lift` gives a unique `q : E/E[N] ⟶ E` with `quotientπ ≫ q = [N]`. Then
   `E/E[N] ≅ E`: `q` is an isogeny of degree `deg[N] / rank E[N] = N²/N² = 1`, hence an iso — **this
   is the degree-facts half**; if it walls (needs `deg`/rank arithmetic on isogenies) decompose+board
   as `[T-G3d-Niso]`. The factored map `q` and `exists_eq_one_add_mulBy_comp_of_fixesTorsion` (the
   T-G3d leaf feeding `aut_endo_eq_one`) follow. The `[N]`-invariance of `[N]` (the input to
   `quotient_lift`) is provable now against the interface (point arithmetic: `mulByHom` additive +
   `t ∈ E[N] ⟹ [N]t = 0`).

## Status / route note
Piece 1 (interface) LANDED. Pieces 2–3 (the construction) are p2-glue-pattern-scale and are the
multi-session bulk; the translation co-action is self-built (no wait on p2's Hopf). Piece 4 (the
consumer) is partly landable now (the factored map via the interface) with the iso-half gated on
isogeny degree facts. Recommended order: 2 → 3 (discharge the pins) → 4; or land Piece 4's factored
map against the interface first (validates the interface end-to-end and advances the T-G3d leaf).
