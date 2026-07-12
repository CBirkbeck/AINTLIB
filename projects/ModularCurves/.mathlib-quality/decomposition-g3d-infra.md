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

1. **[DONE] Interface** (`SubgroupQuotient.lean`) — the categorical-quotient universal property as
   the opaque interface. Consumers touch only this. `quotientπ_hom_ext` proved from `quotient_lift` +
   `quotientπ_isInvariant`. The three DS-data + three pins are the deferred construction.

2. **[DONE] Action legs + the functor-of-points ↔ coequalizer BRIDGE** (`TranslationAction.lean`,
   all axiom-clean). The two coequalizer legs `act, pr_E : G ×_S E ⇉ E` are built in `Over S`:
   `translationAction = (ι ⊗ 𝟙) ≫ μ[E.asOver]` (`= (pr_G ≫ ι) * pr_E` in hom-group form,
   `translationAction_eq_mul`) and `actionProj = pr_E`. The **full bridge**
   `isInvariant_iff_coequalizes : G.IsInvariant f ↔ (act ≫ f = pr_E ≫ f)` is PROVEN both ways
   (`IsInvariant.coequalizes` via the universal points over `G ×_S E`; `IsInvariant.of_coequalizes`
   via precomposition by a chosen point). **This reduces the entire remaining construction to Piece 3.**

3. **Build the coequalizer scheme** `E/G` of `act, pr_E` (+ `quotientπ`, `quotientS`). Once this
   scheme exists, ALL THREE PINS read off mechanically via Piece 2's bridge:
   `quotientπ_isInvariant` = `IsInvariant.of_coequalizes` (π coequalizes by construction);
   `quotient_lift` = coequalizer universal property + `IsInvariant.coequalizes`; `quotientπ_over`
   from `quotientS`. **This is the one genuinely hard, scheme-theoretic piece** (existence of the
   quotient of `E` by a free finite-locally-free action). Two routes:
   - **(3a) affine co-invariant quotient + glue.** Local block: for affine `Spec B ⊆ E`,
     `(Spec B)/G = Spec(B^{coG})`, invariants of the translation co-action `ρ : B → B ⊗_{O_S} O_G`
     (self-built, structure-sheaf dual of `translationAction`; NOT p2's Hopf `subgroupComul`). Glue
     on p2's `SchemeQuotient.lean` glue-data pattern. Mirror p2's `AffineQuotient` for a comodule.
   - **(3b) fppf coequalizer representability.** `E/G` as the fppf-sheaf coequalizer, representable
     because `G` is finite locally free and acts freely (SGA 3 v_III 4.1). Needs p2's fppf engine +
     a representability input.
   p2-stack-scale, a multi-session build; decompose into sub-tickets (co-action `ρ` → affine
   invariants → glue) when started.

4. **[DONE] `[N]`-iso consumer, factored map** (`SubgroupQuotient.lean`) — `mulByHom_torsionSubgroup_isInvariant`
   (`[N]` is `E[N]`-invariant) + `torsionQuotientToSelf` / `torsionQuotientπ_comp_toSelf` (the unique
   `q : E/E[N] ⟶ E` with `π ≫ q = [N]`, via `quotient_lift`). The iso half `E/E[N] ≅ E` (`q` degree
   `deg[N]/rank E[N] = N²/N² = 1`) is the **degree-facts half**, boarded as **[T-G3d-Niso]**.

## Status / route note
Pieces 1, 2, 4 LANDED (all axiom-clean modulo the interface's own DS-pins + p2's BB-QF/BB-FLAT under
`torsionSubgroup`). **The bridge (Piece 2) is the key reduction: the remaining construction is exactly
Piece 3 — build the coequalizer scheme; the three pins then read off through
`isInvariant_iff_coequalizes`.** Piece 3 is the p2-stack-scale scheme-existence piece (route 3a affine
co-invariant quotient + glue, or 3b fppf representability); decompose when started. [T-G3d-Niso] (the
`E/E[N] ≅ E` iso, degree facts) is boarded separately.
