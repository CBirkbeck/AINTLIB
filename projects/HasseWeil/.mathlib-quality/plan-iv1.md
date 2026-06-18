# Development Plan: the IV.1 Formal-Group Program (BRIDGE-003 and friends)

*2026-06-11. Branch `silverman-development`, HEAD cfb13a7. Companion board: `.mathlib-quality/tickets-iv1.md`. Source extraction + code audit (the two inputs this plan is synthesized from) are recorded in the session; key quotes inlined below.*

## Goal

Prove **BRIDGE-003** — the restated `formalIsogenySeries_add` (`FormalIsogenySeries.lean:485`):
for isogenies α, β with x-pullback poles at O and `AddNonInversePair α β`,

```
localExpand W (−(addPullback_x_pair α β) / (addPullback_y_pair α β))
  = HahnSeries.ofPowerSeries ℤ F (MvPowerSeries.subst ![f_α, f_β] (formalGroupLaw W).toMvPowerSeries)
```

(`f_γ := formalIsogenySeries W γ`) — i.e. *the chord–tangent addition, expanded at O, is the formal group law* (Silverman IV §1, pp. 115–120). Downstream payoffs, in order of arrival:
- **Wall A** (`Verschiebung/Genuine.lean:1356` `addPullback_x_pair_x_ord_neg`) closes via the shipped consumer chain (`FIS:1844` + `Genuine:1298` take the BRIDGE-003 conclusion verbatim as `h_iv14`).
- **`formalIsogenySeries_FGL_additivity`** (`GapQfKernel.lean:51`) closes by instantiating at `([k],[1])` + two small connectors; with it, `coeff_one_formalIsogenySeries_mulByInt_eq/_of_neg` (IV.2.3a) go axiom-clean.
- **P** (`GapQfKernel.lean:1244`) closes from the program's substitution keystone (B1/B2) + the proven N, mirroring Silverman IV.4.3's two-line chain-rule proof.
- **BRIDGE-001** (`FIS:360`) closes from P + mem_F; mem_F needs the III.1.5 pair (`GapQfKernel.lean:592/604`) = Phase D (riskiest, isolated: nothing else depends on it).

## References (with print-error warnings)

- [Sil] Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed. In-repo PDF `HasseWeil/Silverman-Arithmetic_of_EC.pdf`, **PDF page = book page + 18** (through Ch. IV; +16 by Ch. VII).
  - IV §1 (pp. 115–120): (z,w)-chart, w(z) recursion + Hensel (IV.1.1, IV.1.2), λ/ν/Vieta/inversion chain, F := i(z₃).
  - IV §2 (pp. 120–122): formal group axioms, [m] recursion, IV.2.3, Lemma 2.4.
  - IV §3–4 (pp. 123–126): invariant differential, IV.4.2 (ω = F_X(0,T)⁻¹dT), IV.4.3 (ω∘f = f′(0)ω).
  - III.1.5 (p. 48): div(ω) = 0 — the two-case affine count + the t-uniformizer computation at O.
- **⚠ VERIFIED PRINT ERRORS in the 2nd ed. (do NOT "fix" code to match the book):**
  - p. 119 line equation: print says `w = λz − ν` with ν = w₁ − λz₁; correct is `w = λz + ν`.
  - p. 119 z₃: print `z₃ = −z₁ − z₂ + (a₁λ + a₃λ² − a₂ν − 2a₄λν − 3a₆λ²ν)/(1 + a₂λ + a₄λ² + a₆λ³)`; **correct** (recomputed two independent ways): `z₃ = −z₁ − z₂ − (a₁λ + a₂ν + a₃λ² + 2a₄λν + 3a₆λ²ν)/(1 + a₂λ + a₄λ² + a₆λ³)`. The legacy Lean `z3 := −B·A⁻¹ − z₁ − z₂` with `B = a₁λ + a₂ν + a₃λ² + 2a₄λν + 3a₆λ²ν`, `A = 1 + a₂λ + a₄λ² + a₆λ³` matches the CORRECT form.
  - p. 120 F display: print's degree-4 part `+(2a₃z₁³z₂ + (a₁a₂−3a₃)z₁²z₂² + 2a₃z₁z₂³)`; **correct**: `−2a₃z₁³z₂ + (a₁a₂−3a₃)z₁²z₂² − 2a₃z₁z₂³`. The legacy hardcoded band (`i+j=4 ↦ (2,2) ? a₁a₂−3a₃ : −2a₃`) matches the CORRECT form.

## The two strategic decisions

**D1 — Keep the legacy `formalGroupLaw`, prove its spec, de-risk the band.** `FormalGroupLaw R` is a bare `MvPowerSeries (Fin 2) R` wrapper (no axiom fields); only 5 facts are proven about the elliptic instance (constant 0, four unit-row coefficients) and **no live consumer needs associativity/commutativity** — the whole downstream chain consumes the identity :485 + those coefficient facts. Silverman himself proves the F-axioms by a one-sentence appeal to the curve's group law (p. 120: *"From properties of the addition law on E, we deduce that F(z₁,z₂) has the corresponding properties"*) — associativity is the single irreducible geometric input and we DON'T NEED IT. What we need is the construction's missing **spec**: `formalGroupLaw W = i ∘ z₃` as series (definitional for degree ≥ 5 via the `bcomp` branch; a finite verification for the hardcoded 2 ≤ deg ≤ 4 band — ticket FG-A6, B2-escape documented). The sorry-free `FormalGroup/` library is used as a proof-pattern donor only (`invariantDiff_chain` for P), NOT a rebuild target.

**D2 — Mirror Silverman's (z,w)-chart derivation; route ALL substitution through `w(z)` only.** The specialization layer never needs Laurent-series substitution (which mathlib lacks). Keystone (B1): for genuine α, `w_α := localExpand(α^*(−1/y)) = PowerSeries.subst f_α (formalW)` by pushing the (z,w)-Weierstrass equation `w = f(z,w)` through the ring hom `localExpand ∘ α^*` and invoking IV.1.1(b)-uniqueness in `F[[z]]` (Hensel, ticket FG-A2). Then `localExpand(α^*x) = f_α / w_α` and `localExpand(α^*y) = −w_α⁻¹` are ring-hom algebra (x = t/w, y = −1/w as functions in KE). The chord is then analyzed in the (z,w) chart: the (z,w)-slope expansion is `subst ![f_α,f_β] λ` by the divided-difference spec (FG-A1 + ring-hom algebra — note: this is NOT the (x,y)-slope `addSlopePair`); the third intersection's z-coordinate is identified by **cubic factorization/Vieta in the Laurent field** (FG-B4, with the tangency/doubling case as its own leaf — Silverman dodges doubling entirely by keeping z₁, z₂ independent indeterminates; we cannot); negation is the i-series ratio spec (FG-A5) applied at the sum point (its curve equation is shipped: `addPullback_pair_equation`).

## Mathlib inventory (verified by the audit)

| Need | Status | Use |
|---|---|---|
| `MvPowerSeries.subst`, `coeff_subst`, `subst_comp_subst`, `subst_X/add/mul` | mathlib `RingTheory/MvPowerSeries/Substitution.lean` | the substitution calculus |
| `PowerSeries.subst` + API, `le_order_subst` | mathlib; project adds `order_subst` equality (`FormalGroup/OrderSubst.lean`) | univariate w∘f |
| `HahnSeries.ofPowerSeries` (+ injective), `X_order_mul_powerSeriesPart`, `ofPowerSeries_powerSeriesPart` | mathlib `LaurentSeries.lean:251-257` | Laurent ↔ PowerSeries descent |
| Laurent substitution | **absent everywhere** | avoided by design (D2) |
| Formal groups | absent from mathlib | n/a (legacy + project library) |

## Project reuse map (the audit's three big finds)

1. `:51` from `:485` by instantiation: `zsmul_genericPoint_eq` (`EC/GenericPointZsmul.lean:409`, unconditional) + `Affine.Point.add_of_X_ne`/`add_self_of_Y_ne` give `addPullback_x/y_pair [k] [1] = mulByInt_x/y (k+1)`; descent via `X_order_mul_powerSeriesPart` + `ofPowerSeries_injective` + shipped positivity (`FIS:1765`). Guards: `mulByInt_x_ne_mulByInt_x` needs `k ≠ ±1`; `k = 1` via the y-leg (`mulByInt_y_one_ne_negY :313`).
2. General-pair Kähler collapse SHIPPED: `kaehler_D_addPullback_x_pair_eq_smul_omega` (`SilvermanIV14:3498`) + `localExpandKaehlerLift` (`GapQfKernel:547`) — available as a cross-check/alternative engine for coefficient extraction on the sum coordinates.
3. P mirrors N: `invariantDiff_localExpand_coeff_zero` (`GapQfKernel:1110`, PROVEN char-free) is the α = id case and the proof template; the abstract chain rule `FormalGroup.invariantDiff_chain` (`FormalGroup/Differential.lean:833`, proven) is the skeleton.

## File plan

- **NEW `HasseWeil/FormalGroupLawSpec.lean`** (Phase A): imports `HasseWeil.FormalGroup`, `Mathlib.RingTheory.MvPowerSeries.Substitution` (+ what compiles). Pure series layer: λ/ν/z₃ as named defs with specs, w-uniqueness, i-ratio spec, the band check, `formalGroupLaw_eq_chord`. Sits below LocalExpansion/FIS (cycle-safe).
- **NEW `HasseWeil/ChordExpansion.lean`** (Phase B): imports `FormalGroupLawSpec`, `FormalIsogenySeries` (hence LocalExpansion, AdditionPullback). The specialization layer + the final `formalIsogenySeries_add` proof. The `:485` statement MOVES here from FIS (grep first: it is sorried with no by-name consumers expected; `Genuine.lean` takes the conclusion as the `h_iv14` hypothesis, not by name). FIS keeps a doc pointer.
- Phases C and D live in the existing files (`Genuine.lean`, `GapQfKernel.lean`) or thin additions.
- Generic orderTop helpers stranded in `SilvermanIV14:841-1256` may be relocated to `HahnSeriesAux.lean` (mathlib-only leaf) IF Phase B needs them below FIS — do lazily, only on demand.

## Dependency graph

```
A1 λ-spec ─┐
A2 w-uniq ─┼─→ B1 w_α = w∘f_α ─→ B2 x/y ─→ B3 slope ─→ B4 Vieta/R₃ ─→ B5 BRIDGE-003
A3 ν,z₃  ──┤                                  (B4a doubling)            │
A5 i-spec ─┤                                                            ├─→ C1 Wall A
A6 band  ──┘                                                            ├─→ C2 :51 → C3 IV.2.3a clean
                                                   B1/B2 ──→ C4 P  ─────┴─→ (with D) BRIDGE-001
D1 div(ω)=0 machinery → D2 :592 → D3 :604 → mem_F
```

## Generality decisions

- Phase A over an arbitrary `Field F` (the legacy `formalGroup*` code's existing context; `[DecidableEq F]` as the file demands). NOT over commutative rings: localExpand/the project lives over fields; ℤ[a₁..a₆]-integrality is Silverman's concern, not ours.
- Phase B over the project's standing `(W : WeierstrassCurve F)`-with-instances context from FIS; no `Fintype`, no `IsAlgClosed`, no `CharP` anywhere in A/B (the chord computation is char-free; doubling handled via the tangent branch, not division by 2).
- All new defs get ≥3 API lemmas; no maxHeartbeats; `classical` only where the surrounding files already use it.

## Risks (named)

1. **A6 band check fails** → the legacy hardcode disagrees with the recursion → B2: restate `formalGroupLaw_coeff` (drop the band, recursion from degree 2), re-prove the 5 coefficient facts, sweep ~12 consumer statements (all witness-parametric — audit verified). Bounded, not fatal.
2. **A5 `formalInverse` recursion ≠ the ratio spec** (zero theorems exist about it) → same B2 shape, smaller blast radius.
3. **B4a doubling** (tangency multiplicity in the cubic factorization) — the genuinely novel formalization step; Silverman's indeterminates dodge it (his z₁, z₂ are never equal; the project's f_α = f_β happens exactly at α = β-as-points). Mitigation: factor-by-division in the Laurent field; tangency = derivative condition from the tangent-slope formula. If stuck: the `kaehler_D_addPullback_x_pair_eq_smul_omega` engine (reuse #2) may supply the doubling-case coefficients independently.
4. **Phase D is certified category-4** by the 2026-05-25 decompose pass (needs ord-on-Kähler at finite points composed with isogeny pullback + the at-∞ leg). It is sequenced LAST, isolated (only BRIDGE-001 consumes it), and has its own mini-decomposition with the III.1.5 source proof. If it stalls, BRIDGE-001 stays an honest guarded sorry and everything else still lands.
5. `MvPowerSeries.subst` over `Fin 2` needs `HasSubst` side conditions (constant coefficient 0) at every composition — the audit confirmed `hasSubst_of_constantCoeff_zero` covers the finite-σ case; threading these is bookkeeping, not math.

## Phase D mini-decomposition (source: III.1.5 proof, book p. 48)

Silverman's proof of div(ω) = 0: (affine) `ord_P(ω) = ord_P(x−x₀) − ord_P(F_y) − 1 = 0` via the dichotomy {ord_P(x−x₀) = 1, F_y(P) ≠ 0} vs {ord_P(x−x₀) = 2, F_y vanishes simply} (2-torsion split); (at O) `ω = (−2f + tf′)/(2g + a₁tf + a₃t³) dt` with x = t⁻²f, y = t⁻³g, value −2f(O)/2g(O) ≠ 0 for char ≠ 2; char 2 via ω = dy/F_x. The project shape: a_α = Dω(α^*x)/α^*u (shipped `Dω_isog_pullback_x_gen`); :592 (no finite poles) needs ord_P(a_α) ≥ 0 at every smooth P — including kernel points where both numerator and denominator have poles; :604 is the at-∞ leg, where `RamificationInfty`-style sign preservation must be ported to the bare `Isogeny`. D-tickets carry this split; D is allowed to end REVIEW-PENDING if the kernel-point pole cancellation needs machinery the file lacks.
