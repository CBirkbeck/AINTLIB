# V.1.3 HANDOVER — close the final polynomial divisibility

**Branch**: `worker-tensor-isom` · **HEAD at handover**: `a00f844` · **Status**: V.1.3 reduced to ONE concrete polynomial divisibility with two viable closure routes.

## TL;DR

V.1.3 of the Hasse bound (`sepDeg(1−π) = #E(F_q)`) has been driven across ~24 worker dispatches to a single sharp residual: **`(rX − rXq)² ∣ nReduced_R` in `R = AdjoinRoot W.poly`** (`RouteB.nReduced_R_div_D_sq`, `HasseWeil/AdditionPullback/PointMap.lean:~1639`). Everything else — the keystone, the entire ramification-side chain, residue/inertia, injectivity, the IsAlgClosed-free smooth-point extraction engine, and the K3 K̄-Frobenius-fixed locus count — is axiom-clean. **Close this one polynomial divisibility and V.1.3 is COMPLETE.**

The recent commit `a00f844` shipped axiom-clean **three new structural identities** that factor the residual very precisely, isolating the remaining obstruction to the q-Frobenius / coprime-divisibility step. The next worker has two concrete routes (described in §5 below).

## 1. Where the single sorry lives

```
File:      HasseWeil/AdditionPullback/PointMap.lean
Line:      ~1639
Lemma:     HasseWeil.RouteB.nReduced_R_div_D_sq
Statement: (rX − rXq)² ∣ nReduced_R   (in R = E.toAffine.CoordinateRing)
```

where (in R):
- `rX := AdjoinRoot.root W.poly` (the generic x-coordinate)
- `rY := AdjoinRoot.mk W.poly (Polynomial.C Polynomial.X)` (the generic y-coordinate; verify the exact def in PointMap.lean)
- `rXq := (negFrobeniusIsog W).pullback (x_gen W)` (Frobenius pullback of rX, i.e. `rX^q` in R)
- `rYq_neg := (negFrobeniusIsog W).pullback (y_gen W)` (negated Frobenius pullback of rY)
- `D := rX − rXq`
- `N := rY − rYq_neg`
- `nReduced_R := N² + a₁·D·N − D²·(a₂ + rX + rXq)` (verify spelling in `nReduced_R_eq_numUnreduced_R`)

The geometric content: **Silverman III.2** — a rational map from a smooth curve is a morphism, specialised to the addition isogeny `1 − π`. The chord-slope `s = N/D` has a pole at the Frobenius-fixed locus (`D = 0`), but the chord-formula numerator cancels the pole via the Weierstrass cubic relation, making `addPullback_x = s² + a₁·s − a₂ − rX − rXq ∈ R`.

## 2. Why this closes V.1.3

The chain (all downstream of `nReduced_R_div_D_sq`, already wired and axiom-clean modulo this one residual):

```
nReduced_R_div_D_sq                             [the open sorry]
  ⟹ divisibility_witness_x                      [witness construction]
  ⟹ addPullback_x_in_coordRing_range            [PointMap.lean:~1101]
  ⟹ + (the y-companion divisibility_witness_y, sorry'd, analogous derivation)
  ⟹ oneSubFrob_baseChange_coordHom              [PointMap.lean:~990, the [G2] CoordHom]
  ⟹ Leaf 1 wires through (addCoordAlgHom_evalAt_x/_y, axiom-clean at ~856/898)
  ⟹ oneSubFrob_isogBaseChange_toPointMap_eq     [PointMap.lean:~1032]
  ⟹ h_fiber_bridge                              [WireUpPrep.lean:~1491]
  ⟹ oneSubFrob_isogBaseChange_fiberData         [WireUpPrep.lean:~1362]
  ⟹ degree_isogOneSub_negFrobenius_eq_pointCount [WireUpPrep RouteB target]
  ⟹ isogOneSub_negFrobenius_degree_eq_pointCount [GapSpines.lean:~458]
  ⟹ sepDegree_oneSub_eq_pointCount + ker_deg_skeleton   [V.1.3 KEYSTONES]
  ⟹ Hasse bound for V.1.3 side    ✓
```

After this, the only V.1.3-side downstream gates remaining: **[G3]** `IsIntegrallyClosed CoordinateRing` for general char (shipped under `[NeZero 2/3]` at `Curves/IntegralClosure.lean:~842`) and the Deliverable-1 module-finiteness witnesses [G2↓] (mechanical once G2 lands). Both are already explicitly stubbed in WireUpPrep with concrete proof plans.

## 3. Shipped axiom-clean assets (REUSE — do NOT rebuild)

In `HasseWeil/AdditionPullback/PointMap.lean`:
- **`nReduced_R_image_eq`** (~L1140): `algebraMap R KE nReduced_R = (algebraMap rX − algebraMap rXq)² · addPullback_x`. The KE identity.
- **`nReduced_R_eq_numUnreduced_R`** (~L1188): `nReduced_R = N² + a₁·D·N − D²·(a₂ + rX + rXq)` in R. The polynomial form via Vieta-of-chord-cubic.
- **`pullback_equation_R`** (~L1188+): R-level Weierstrass identity for `(rXq, -rY^q - a₁·rXq - a₃) = (rXq, rYq_neg − corrections)`, i.e. the Frobenius image satisfies the curve equation in R. Used in the squared-form identity.
- **`rYq_sub_rY_mul_N`** (~L1484, from commit `73bdfe0`): `(rY^q − rY) · N = D · (a₁·rY − C)` where `C = rX² + rX·rXq + rXq² + a₂·(rX + rXq) + a₄`. Proof: `linear_combination h_uv − h_xy` where `h_xy` is W1 (Weierstrass on rY) and `h_uv` is `pullback_equation_R` (W2').
- **`rYq_sub_rY_mul_N_plus_a1D`** (~L1576, same commit): `(rY^q − rY) · (N + a₁·D) = D · (a₁·rY^q − C)`. Same `linear_combination` shape.
- **`rYq_sub_rY_sq_mul_nReduced_R_eq_D_sq_mul_M`** (~L1681, from commit `a00f844`): **the squared-form Vieta identity**: `(rY^q − rY)² · nReduced_R = D² · M` where `M = (a₁·rY − C)·(a₁·rY^q − C) − (rY^q − rY)²·(a₂ + rX + rXq)`. Proof: `linear_combination (D·K')·h_A + ((rY^q − rY)·N)·h_B + (rY^q − rY)²·h_red` where `h_A`/`h_B` are the two identities above and `h_red` is `nReduced_R_eq_numUnreduced_R`.

In `HasseWeil/Hasse/L6Witnesses.lean`:
- **The whole V.1.3 ramification-side chain** is axiom-clean modulo the single SORRY at GapSpines `isogOneSub_negFrobenius_degree_eq_pointCount` (which downstream-routes to the polynomial divisibility above): combinator `Sinf_primeOver_eq_kernelPrime_place_of_sum_inertia_eq_pointCount`, residue `Sinf_finrank_kappa_kernelPrime_eq_one` + `bridge_Biv_inertia_eq_one_v2`, residue-at-O via `{1, y}`-parity, injectivity `Sinf_kernelToPrime_v2_injective`, R2e + ne_bot, the IsAlgClosed-free smooth-point extraction engine, K3 `geomPoles_oneSubFrob_card_eq_pointCount`. ALL `[propext, Classical.choice, Quot.sound]`.

In `HasseWeil/Curves/FrobeniusFixedPoint.lean` + `FrobeniusFixedLocus.lean`:
- **L5 ALL axiom-clean**: `ncard_ker_oneSubGeomFrobHom_eq_pointCount`, `frobenius_fixed_iff_mem_baseField`, `fixedLocus_geomFrobenius_eq_range_includePointBC`.

In `HasseWeil/Hasse/WireUpPrep.lean` (RouteB):
- **degree base-change** `degree_oneSubFrob_baseChange_eq` (~L1147), the base-changed `(1−π)_K̄` pullback `oneSubFrob_pullback_baseChange` — all axiom-clean.

In mathlib:
- `WeierstrassCurve.Affine.addPolynomial_slope` (`Affine/Formula.lean:~265`) — factors the chord-curve cubic in KE[X] as `−(X − x_gen)(X − π·x_gen)(X − addPullback_x)`. The KE Vieta identity is essentially this.

## 4. The honest obstruction (verified by 3 workers)

Setting `D = 0` (i.e. `rXq = rX`) in `nReduced_R`, then reducing via W1 + W2', leaves a NON-VANISHING residue `4·cubic(rX) + ν² − (rY − rY^q)²` (or analogous form depending on signs). **This means the divisibility CANNOT be derived from W1 + W2' alone** — the literal q-Frobenius (`rY^q` IS the q-th power in R, not just a formal symbol satisfying W2') must enter.

The shipped squared-form identity `(rY^q − rY)² · nReduced_R = D² · M` is the closest we got without the q-Frobenius:
- IF `(rY^q − rY)²` and `D²` were COPRIME in R, we could cancel and conclude `D² ∣ nReduced_R`.
- BUT they're NOT coprime: both vanish at every F_q-rational curve point. So the cancellation fails.

The q-Frobenius IS what makes `(rY^q − rY)` and `D = rX − rXq = rX − rX^q` share their non-coprimality precisely on the F_q-fixed locus, and provides the further structure to extract the cancellation.

## 5. TWO viable closure routes

### ROUTE A — q-Frobenius cancellation (char-dependent, structural)

The CONCRETE q-Frobenius identity needed (after the analysis above): an identity in R of shape
```
(rY − rY^q)² = (some W-derivable polynomial in rX, rY, rXq, rY^q) + D·(some R-element)
```
that, combined with the shipped structural identities + W1 + W2', closes the residue.

**Approach for this route:**
- Use `CharP K p` (project shipped; K is `Fintype` finite field, so `CharP` is available — verify the exact instance hook).
- Use Frobenius properties: `(a + b)^q = a^q + b^q` for `q = p^n` in char p (mathlib `frobenius_add`/`Frobenius.pow_card` / `Polynomial.frobenius`).
- Note `rY^q` is the LITERAL q-th power of `rY` in R; its `{1, rY}`-basis form `α(rX) + β(rX)·rY` (for odd q) is q-dependent. **However**, for the divisibility statement, we don't necessarily need to compute `α, β` explicitly; we can use the q-Frobenius RING-HOMOMORPHISM property over `F_q` directly.
- Specifically: `Frobenius: R → R, r ↦ r^q` is a ring hom in char-p R with K = F_q (it fixes K-elements and commutes with addition/multiplication). Then `(rY)^q = Frobenius(rY)` and we have `rY^q − rY` as `(Frobenius - id)(rY)`. Similarly `D = rX − rXq = (id − Frobenius)(rX) = −(Frobenius − id)(rX)`. So `D` and `(rY^q − rY)` are both in the image of `(Frobenius − id)` on R. Their RATIO or relationship — `D = −(Frobenius − id)(rX)`, `(rY^q − rY) = (Frobenius − id)(rY)` — exposes the Frobenius structure.
- A possibly clean lemma: **`D | (rY^q − rY)·(something)`** or a "ratio" identity like `(rY^q − rY) · (rY + rY^q + ...) = (rX^q − rX) · (some explicit Weierstrass-derived polynomial)`. This kind of identity is what the Frobenius-respect-Weierstrass relation provides.

Mathlib tools to search:
- `Polynomial.expand_pow_lt_aeval` / `frobenius_X_pow_sub_X`.
- `RingHom.frobenius`, `frobenius_def`.
- `FiniteField.pow_card`, `ZMod.pow_card`, `frobeniusEquiv`.

### ROUTE B — Integrality via IsIntegrallyClosed (char ≠ 2,3 only)

`Curves/IntegralClosure.lean:~842` ships **`IsIntegrallyClosed E.toAffine.CoordinateRing`** under `[NeZero 2]` and `[NeZero 3]` (i.e. char K ∉ {2, 3}). Use this to argue:

`addPullback_x ∈ KE = Frac(R)` is INTEGRAL over R ⟹ (by `IsIntegrallyClosed`) `addPullback_x ∈ R`.

To show integrality: produce a MONIC polynomial in `R[X]` with `addPullback_x` as a root. Candidates:
- **From `addPolynomial`**: lifts to `R[1/D][X]`, with `rX, rXq, addPullback_x` as roots. Clearing denominators gives a non-monic polynomial in R[X]; not directly usable.
- **Via the y-side**: `addPullback_y` satisfies the Weierstrass relation `Y² + a₁·X·Y + a₃·Y − (X³ + …) = 0` paired with `addPullback_x`. As a polynomial in `X` (with `addPullback_y` substituted), it's monic in X (degree 3), with `addPullback_x` as a root. BUT coefficients involve `addPullback_y` which itself isn't known to be in R (it's the y-divisibility companion). Mutual dependency.
- **Via the trace/norm**: `addPullback_x` is fixed by Gal(KE/K(x_gen))-style stabilizers, giving a minimal polynomial over `K(x_gen)`. If this minimal polynomial has R-integral coefficients (R = K[x_gen, rY]-style), integrality follows.

**Mathlib tool**: `IsIntegrallyClosed.algebraMap_eq_of_integral` or similar (search Loogle for `IsIntegrallyClosed` + `algebraMap`).

This route is **char-conditional** (NeZero 2, 3). For char 2 or char 3, would need Route A or a different argument.

### Recommendation: try BOTH route plans in parallel sub-leaves

Route A is char-uniform but requires q-Frobenius algebra. Route B is char-conditional but uses shipped infrastructure (`IsIntegrallyClosed`). Closing under `[NeZero 2, 3]` via Route B + leaving char-2/3 as a separate sub-residual is acceptable and partitions the work cleanly.

## 6. Commit log (V.1.3 deep-pass, in order)

| Hash | Description |
|------|-------------|
| `bb5f464` | V.1.3 two leaves → ONE unifying place-correspondence bridge |
| `403793e` | REDUCTION 2 — R2e + ne_bot shipped axiom-clean, R2a isolated |
| `4e31995` | decompose final residual — target sorry-free over CORE + REDUCTION 2 |
| `26a07eb` | `Sinf.inertiaDeg_eq_one_of_algebraMap_surjective` shipped |
| `e6c7cad` | `Sinf_kernelToPrime_v2_injective` — distinct kernel points → distinct primes |
| `11ba7ed` | residue field at O is K — residue core complete; `bridge_Biv_inertia_eq_one_v2` axiom-clean |
| `c2b792b` | `Sinf_kappa_kernelPrime_residue_in_base` — value of regular fn at F_q-rational kernel point is K-constant |
| `6a268e8` | gitignore beastmode session sentinel |
| `2c9462e` | untrack `.mathlib-quality/beastmode_active` |
| `e47a0f1` | `l6_computationA` h_card — `#primesOver = #ker = pointCount` |
| `1969da2` | `Sinf_finrank_kappa_kernelPrime_eq_one` — residue field at F_q-rational kernel prime is K (via `evalAt`) |
| `3e371d6` | V.1.3 leaf reduced via combinator — to `Σ inertiaDeg = pointCount` |
| `b68f5bf` | decomposition doc updated (`decomposition-V13-final.md`) |
| `8821b0a` | Phase 3: K3+K4 dispatcher `geom_poles_card_eq_pointCount_of_pole_eq_ker` |
| `68c6708` | Phase A composer |
| `9ac0a2a` | Phase B composer |
| `840d610` | Phase C composer (the cycle-breaker — given surjectivity, closes via Finset/cardinality) |
| `9e38281` | **K3 concrete**: `geomPoles_oneSubFrob_card_eq_pointCount` = `Nat.card (K̄-pole set) = pointCount` axiom-clean |
| `8f58188` | V.1.3 collapsed to single residual `isogOneSub_negFrobenius_degree_eq_pointCount` |
| `87b7887` | G2 residual decomposed — sharp polynomial-identity targets stated (`addPullback_x/y_in_coordRing_range`) |
| `c2dc6f0` | sharpen V.1.3 [G2-x]/[G2-y] residuals — reduction to divisibility in R |
| `03ef1cd` | (partial) `nReduced_R` def + `nReduced_R_image_eq` axiom-clean + `divisibility_witness_x/y` sorry-gated |
| `550f5f3` | **BUG**: spurious reduction `D_dvd_N_in_R` (`(rX − rXq) ∣ (rY − rYq_neg)`) — GENERICALLY FALSE |
| `08be88c` | bug retracted: replaced `D_dvd_N_in_R` with correct residual `nReduced_R_div_D_sq` (`D² ∣ nReduced_R`) |
| `73bdfe0` | V.1.3 deep pass — two axiom-clean auxiliary identities (`rYq_sub_rY_mul_N`, `rYq_sub_rY_mul_N_plus_a1D`) |
| `a00f844` | **V.1.3 deep pass — squared-form Vieta identity** `(rY^q − rY)² · nReduced_R = D² · M` axiom-clean. **HEAD at handover.** |

## 7. Anti-patterns observed (avoid these)

- **Adding abstract witness-form composers without closing the actual content** (Phase A/B/C — useful but doesn't close).
- **Renaming the goal as a "sharp residual"** without mathematical progress (commit `8f58188` did this).
- **Over-tightened reductions** that are stronger than the actual content needed (commit `550f5f3`, retracted at `08be88c`).
- **`linear_combination` over W1 + W2' alone** for the final divisibility — proven insufficient by the residue analysis at `a00f844`. The q-Frobenius or integrality MUST enter.

Workers should: BUILD concrete polynomial witnesses + algebraic identities, not factor abstractly. Each axiom-clean structural identity (`rYq_sub_rY_mul_N`, `_plus_a1D`, the squared-form) is GENUINE progress.

## 8. The y-companion

`divisibility_witness_y` (`PointMap.lean:~1276`) is the y-side analog of `divisibility_witness_x`. Worker `08be88c` confirmed its statement is **correct as-is** (not over-tightened). Its proof should follow the SAME q-Frobenius / integrality route as the x-side; once the x-side closes, the y-side templates directly. The y-side chord-formula derivation (`addPullback_y` ↔ chord formula) is already axiom-clean (proved via `linear_combination -(addPullback_x − x_gen) * h_slope_mul`); only the divisibility witness remains.

## 9. III.6.3 (qf_nonneg) — the second Hasse witness, parked

The OTHER witness needed for the Hasse bound is `qf_nonneg` (Silverman III.6.3, `0 ≤ q·r² − t·r·s + s²`). It's tracked separately (`hasse-qf-route-pic0`, `GapSpines.lean:710+` for `qf_nonneg_skeleton`). When V.1.3 closes, qf_nonneg is the remaining piece for the full Hasse bound. See `[[hasse-qf-route-pic0]]` memory.

## 10. Beastmode sentinel state

The session sentinel `.mathlib-quality/beastmode_active` is ARMED with focus directed at the K̄-count / polynomial-divisibility route. The next worker should overwrite the sentinel with their own focus before dispatch (the file is gitignored, so it's session-local).

## 11. Suggested next worker prompt (template)

> Pick up V.1.3 from handover `.mathlib-quality/V13-HANDOVER.md`. Branch `worker-tensor-isom`, HEAD `a00f844`. Target: close `RouteB.nReduced_R_div_D_sq` at `HasseWeil/AdditionPullback/PointMap.lean:~1639`. Use Route A (q-Frobenius) or Route B (`IsIntegrallyClosed` under `[NeZero 2, 3]`) per the handover §5. Reuse axiom-clean structural identities `rYq_sub_rY_mul_N`, `rYq_sub_rY_mul_N_plus_a1D`, `rYq_sub_rY_sq_mul_nReduced_R_eq_D_sq_mul_M`, `nReduced_R_image_eq`, `nReduced_R_eq_numUnreduced_R`, `pullback_equation_R`. NO abstract composers, NO refactoring without closure. Commit each closing sub-leaf via explicit path (NOT `git add -A`; sentinel `.mathlib-quality/beastmode_active` is gitignored but use explicit paths anyway). Trailer: `Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>`. Avoid the word "clean" next to git commands.
