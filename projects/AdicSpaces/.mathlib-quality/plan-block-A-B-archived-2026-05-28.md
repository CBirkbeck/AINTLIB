# Development Plan: Close `tateAcyclicity` (Wedhorn Thm 8.28(b))

**Target**: make `ValuationSpectrum.tateAcyclicity`
(`Adic spaces/LaurentRefinement.lean:3671`) sorry-free under the signature
`[IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
(P : PairOfDefinition A) [IsNoetherianRing P.A₀]
(C : RationalCovering A) (hne : C.covers.Nonempty)`.

No signature pollution (no `[IsDomain A]`, no `[DiscreteTopology A]`,
no `MulArchimedean`, no `hZavyalov` leaks).

## Current sorry inventory (Tate-core critical path)

Tate-core sorries, located via
`awk '/^[[:space:]]*sorry[[:space:]]*$/ {print NR": "FILENAME}' "Adic spaces"/*.lean`:

| Location | Content | Blocker |
|---|---|---|
| `LaurentRefinement.lean:3173` | `laurentOverlapBridge_exists_compatible` | bivariate Example 6.38 (T-OV-1) |
| `LaurentRefinement.lean:3737` | `tateAcyclicity` Part 2 (gluing) | depends on overlap bridge + refinement transfer |
| `PresheafTateStructure.lean:1322` | `restrictionMapHom_injective` | algebraic: NZD of `mk(D₀.s)` in `A⟨X⟩/(1-D.s·X)` + faithful-flatness |
| `PresheafTateStructure.lean:1208` | `restrictionMap_isLocalization` / sigma surj (Wedhorn Prop 8.15) | Baire category / Wedhorn Prop 8.15 |
| `StructureSheaf.lean:1096` | `isSheafy_ofStronglyNoetherianTate_flat.embedding` | topological inducing (off the tateAcyclicity critical path) |
| `Presheaf.lean:720` | `spa_point_nonOpen_of_rational_subset` | Bourbaki CA III §2.8 (**retired** from critical path) |

## Infrastructure already in place (complete, no sorry)

- `Adic spaces/Cor832.lean` (1357 lines, 0 sorry) — full Cor 8.32 framework
  reduced to the clean residual `coeRingHom_preserves_proper`
  (`productRestriction_injective_tate_via_coeRingHom_preserves_proper`,
  line 1202). Uses the Bourbaki-blocked closedness question as the single
  remaining algebraic input.
- `Adic spaces/Example638.lean` (1501 lines, 0 sorry) — generic Example 6.38
  plus + minus equivs over arbitrary complete strongly noetherian Tate base.
- `Adic spaces/StandardCover.lean` (733 lines, 0 sorry) — standard-cover
  reduction `refines_by_standard_cover` conditional on `hZavyalov` hypothesis
  (adic Nullstellensatz, Wedhorn Prop 7.14 content).
- `Adic spaces/ValuationSpectrumCompact.lean` (1035 lines, 0 sorry) — Huber
  compactness port: `CompactSpace (Spv A)`.
- `Adic spaces/SpaCompact.lean` (460 lines, 0 sorry) — `CompactSpace ↥(Spa A A⁺)`
  for discrete and Tate cases.
- `Adic spaces/Cor732.lean` (292 lines, 0 sorry) — Wedhorn Cor 7.32 dominating
  unit extraction.
- `Adic spaces/RationalRefinement.lean` (0 sorry) —
  `separation_of_finer_rational`, `gluing_of_finer_rational`.

### Bridge chain (all 0 sorry)

- `laurentPlusBridge`, `laurentMinusBridge`: complete via Example 6.38
  instantiation at `B := presheafValue D₀`.
- `laurentPlusBridge_restrictionMap`, `laurentMinusBridge_restrictionMap`:
  complete via the iterated-rational equivs' action on `canonicalMap`.
- `presheafValue_iteratedPlus_equiv`, `presheafValue_iteratedMinus_equiv`
  (Wedhorn Lemma 2.13): complete, all continuity and round-trip obligations
  discharged.
- `laurentCover_gluing_presheaf`: proved via `laurentCover_gluing_presheaf_viaRow3`
  + the four Route-B bridges + `laurentBridge_delta_eq_zero_of_compat`.
- `laurentBridge_delta_eq_zero_of_compat`: proved modulo
  `laurentOverlapBridge_exists_compatible` (the remaining sorry).

## Remaining work to close `tateAcyclicity`

### Critical path

**Block A — Part 1 (separation):** close `restrictionMapHom_injective`
(`PresheafTateStructure.lean:1322`). Options:
- **A.1** (current path): direct algebraic proof via the Example 6.38 iso
  + the NZD claim on `mk(D₀.s)` in `A⟨X⟩/(1-D.s·X)`. Partially discharged
  (T-INJ-NZD done: `mk(D₀.s)` IS a unit under iso-hypotheses); remaining gap
  is the asymmetric NZD argument for the source.
- **A.2** (alternative): via
  `productRestriction_injective_tate_via_coeRingHom_preserves_proper`
  + the Bourbaki-blocked `coeRingHom_preserves_proper`
  (`Loc.Away/s / q → presheafValue D / q̂` is proper for `q ≠ ⊤`).
  Closed transitively by T-IDEAL-1 (approximation, DONE) + T-IDEAL-2
  (closedness, BLOCKED on Bourbaki CA III §2.8).

**Block B — Part 2 (gluing):** close `tateAcyclicity` Part 2 sorry
(`LaurentRefinement.lean:3737`). Route:
1. Close `laurentOverlapBridge_exists_compatible` (B.1 below).
2. Use `tateAcyclicity_gluing_via_refinement` + `refines_by_standard_cover`
   + Laurent-cover induction to transfer gluing from Laurent base to general
   rational cover. This requires either closing `hZavyalov` unconditionally
   (Wedhorn Prop 7.14) or finding an alternative refinement existence result.

**Block B.1 — bivariate Example 6.38 primitive (T-OV-1):** build
`presheafValue(overlap_B) ≃+* B₁₂_gen(b)` over an arbitrary complete
strongly noetherian Tate base `B` and `b ∈ B` power-bounded in both
directions. This is the "bivariate Laurent analog" of Example 6.38 and
requires defining an `evalBivariateHom` with `ζ ↦ b, ζ⁻¹ ↦ b⁻¹`.

Estimated effort: ~500 lines. Major undertaking.

### Non-critical-path

- `restrictionMap_isLocalization` / sigma surj (`PresheafTateStructure.lean:1208`):
  Baire category / Wedhorn Prop 8.15. Not needed for the Route-B closure
  of Part 2 (which uses bridges + delta-vanishing, not sigma surj).
- `isSheafy_ofStronglyNoetherianTate_flat.embedding` (`StructureSheaf.lean:1096`):
  topological inducing. Downstream of `tateAcyclicity`.
- `spa_point_nonOpen_of_rational_subset` (`Presheaf.lean:720`):
  Bourbaki-blocked. Retired from critical path per the 2026-04-15 reviewer.

## Immediate options for next session(s)

1. **T-OV-1 / T-OVERLAP-COMPAT** (~500 lines, 1-2 sessions): build the
   bivariate Example 6.38. Closes `laurentOverlapBridge_exists_compatible`.
   Unblocks Block B.
2. **Bourbaki CA III §2.8 port** (~300-600 lines, 2-3 sessions): formalise
   `Submodule.isClosed_of_fg` for complete T2 linearly-topologized rings.
   Closes T-IDEAL-2, unlocks `coeRingHom_preserves_proper`, which together
   with T-IDEAL-1 closes Block A via alternative A.2.
3. **Wedhorn Prop 7.14 port** (adic Nullstellensatz, ~300+ lines): closes
   `hZavyalov` hypothesis unconditionally. Required for `tateAcyclicity`
   Part 2 via the standard-cover reduction even after Block B.1 closes.
4. **Algebraic NZD for source (Block A.1)**: pursue the asymmetric NZD
   argument on `D.s` in `A⟨X'⟩/(1-D₀.s·X')` — unclear if this is simpler
   than the Bourbaki path.

## Risk

All four remaining directions require substantial new infrastructure:
- T-OV-1 is pure algebraic but long (bivariate Tate algebra machinery).
- Bourbaki is a Mathlib contribution; upstream dependency.
- Prop 7.14 is Wedhorn-style valuation-theoretic.
- Algebraic NZD route is unscoped.

No single session closes `tateAcyclicity` fully.

## Current state document provenance

This file generated 2026-04-16 from direct inspection of the codebase
(`awk` on `sorry` lines, `grep` on theorem/definition structure). Supersedes
all prior plans in `docs/plans/` for the acyclicity proof; see
`docs/plans/2026-04-14-acyclicity-completion.md` for the historical
roadmap and `docs/plans/2026-04-16-part2-route.md` for the Part 2 routing
analysis.
