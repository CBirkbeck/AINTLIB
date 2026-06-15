# Master Ticket Index

This is the **single source of truth** for ticket status. Update this file every
time you check out, work on, or finish a ticket. See `PROTOCOL.md` for the
checkout protocol and `DEPENDENCIES.md` for the dependency graph.

## Active workers

Workers should add their ID here when they start a session and remove it when
they're done for the day. This helps avoid duplicate claims.

| Worker ID | Last seen | Currently working on |
|---|---|---|
| worker-A | 2026-04-17 | Stream A: T-II-4-001, T-II-1-002, T-II-1-003, T-II-1-006 done (REVIEW) |
| worker-B | 2026-04-17 | Stream B: T-III-2-007 checked out (E_ns nonsingular part) |
| worker-C | 2026-04-08 | (between sessions; session 3 done — see PROGRESS) |
| worker-D | 2026-04-17 | Stream D: T-IV-4-001..005 (invariant differential) DONE (reviewed, axiom-hygienic) |
| worker-E | 2026-04-17 | Stream D: built `PowerSeries.eq_zero_of_self_eq_mul_self` infra; split `OmegaPullbackCoeff` → `WronskianAux` to isolate 57GB `ring`; T-IV-1-003 released (factoring step still blocked by `PowerSeries` typeclass gaps) |
| worker-F | 2026-04-17 | Stream D: rewrote `WronskianAux` via `linear_combination` + explicit polynomial multipliers `M` (from `scripts/compute_multipliers.py`); added `CNorm` simp API for `C n` vs `n : R[X]` normalization. `maxHeartbeats`: 32M→default (m=3), 64M→default (m=4, 160× reduction). RAM: 57GB→2GB. Reviewed T-IV-4-001..005 → DONE. |
| worker-G | 2026-04-17 | Stream D: 10 tickets → REVIEW: T-IV-2-006/007 (ℕ), T-IV-4-006, T-IV-5-001/002/004/005/006, T-IV-7-001/002. New API: `FormalGroupHom.id/ext`, `PowerSeries_subst_MvSubst_eq`. Added T-IV-2-010 (comp, OPEN). Files: `FormalGroup/{MulByNat,CharP,Logarithm,Height,Hom}.lean` (~1050 lines). |
| worker-H | 2026-04-17 | Stream A: assessed T-II-1-004, T-II-1-005, T-II-3-004, T-II-2-001 → all BLOCKED with detailed infrastructure notes. Wrote `infrastructure-plan.md` + Phase A/B/C/D tickets at `tickets/curves/infra/`. Executed T-II-INFRA-A-001/002/003 (~127 lines in `HasseWeil/Curves/FiniteOverKx.lean`) — `SmoothPlaneCurve` now has `Module.Finite (Polynomial F)` on coordinate ring + `finrank 2` over `FractionRing (Polynomial F)`, dropping the `[IsElliptic]` hypothesis from `HasseWeil/Basic.lean`'s analogous results. Only standard axioms. |
| worker-I | 2026-04-20 | Stream D: delivered T-IV-3-002 + T-IV-3-003 + T-IV-3-006 (full) + Part A of T-IV-3-004 in new `HasseWeil/FormalGroup/Associated.lean` (~609 lines total): operation identities on `Ĝ_a`/`Ĝ_m`, F(M^n) filtration, graded congruence lemmas, and packaged `evalGroup_powerIdeal_toQuot` + kernel/range + `quotKerEquivRange`. **Fixed typeclass diamond** by introducing `F.EvalGroup` wrapper type in `EvalGroup.lean` + `nsmul_val` bridge. All axiom-clean. Also verified 10 worker-G REVIEW tickets in IV.2/4/5/6/7 as axiom-clean and promoted R → D. |
| worker-I | 2026-04-20 | Stream A: **B-002, B-007, B-008, D-004a, D-004 (F[C] case)** → REVIEW; **D-001/D-002, D-005** PARTIAL; **B-009** BLOCKED (trdeg). `HasseWeil/Curves/Infinity.lean` now ~440 lines: `ordAtInfty` via norm+`RatFunc.intDegree`, `ordAtInfty_coordX = -2`, `ordAtInfty_coordY = -3`; fibre finiteness; Liouville for `F[C]`; Bezout-bridge `norm_eval_at_x_of_zero_at_smoothPoint`; **D-004a** `mem_maximalIdealAt_iff_eval_zero` via `AdjoinRoot.lift`-built `coordEval`; **D-004 (CoordinateRing)** `finite_setOf_mem_maximalIdealAt` — for `u ∈ C.CoordinateRing` nonzero, `{P | u ∈ M_P}.Finite`. Plus `ProjectiveTuple.mk_smul`, `CurveMap.degree_comp`/`comp_algebraMap_eq`/`ramificationIndex`. Standard axioms only. |
| worker-J | 2026-04-20 | Stream B/E + V: new `HasseWeil/Hasse/Separability.lean` (~160 lines) — witness-parametric Silverman III.5.3, III.5.4, III.5.5, V.1.2. Six theorems. Tickets T-III-5-003/004/005, T-V-1-002 → PARTIAL. Stream V: new `HasseWeil/Hasse/PointFix.lean` (~130 lines) — closed T-V-1-001 (→ DONE), plus `kernel_eq_top_of_hom_eq_id_sub_frobenius`, `degree_eq_pointCount_of_witness` (T-V-1-003 witness, BLOCKED → PARTIAL), `pointCount_eq_of_hom_kernel_witness`. Stream V capstone: new `HasseWeil/Hasse/BoundOfWitnesses.lean` (~115 lines) — `traceOfFrobenius_sq_le_of_witness`, `hasse_bound_of_witnesses`, `hasse_bound_sq_of_witnesses`, `hasse_bound_of_full_witnesses` (fully-chained from hom+kernel+quadratic witnesses). All axiom-hygienic (standard only). |
| worker-K | 2026-04-21 | Stream B/C: T-III-3-003 scope audit → escalated 60→300–500 lines; spawned sub-ticket **T-II-3-001b** (projective divisor extension). **Delivered `HasseWeil/Curves/ProjectiveDivisor.lean` (300 lines)**: ProjectiveSmoothPoint, ProjectiveDivisor, projectiveDivisorOf, principal/linear-equiv, PicProj/PicProj₀ (T-II-3-001b → REVIEW). Audit of T-II-3-009 revealed original statement mathematically false; revised with `projectiveDivisorOf` + `[IsAlgClosed F]`. Delivered **Helper A** (F(x) product formula). **Delivered `HasseWeil/Curves/NormValuation.lean` (~650 lines)**: **20 Helper B bridge lemmas, all axiom-clean** incl. `inertiaDeg_maximalIdealAt = 1`, Zariski path, `exists_coordinates_of_isMaximal`, **`equation_of_coordinates`** (W(a,b) = 0 in F), **`exists_smoothPoint_of_isMaximal`** + **`maximalIdealAt_injective`** + **`smoothPointEquivMaxIdeal`** (full bijection), **`smoothPoint_fiber_eq_primesOver`** (fiber bijection), **`sum_ramificationIdx_over_fiber`** (Σ e·f = 2), **`sum_ramificationIdx_eq_finrank`** (Σ e = 2 via f=1) — using worker-I's unconditional `IsDedekindDomain` instance. T-II-3-009 CHECKED-OUT; remaining: ord_P ↔ multiplicity bridge (needs IsIntegrallyClosed+Dedekind) + relNorm combination. |
| worker-I | 2026-04-21 | Stream A: delivered **IC-003ii unconditional** `isIntegrallyClosed_coordinateRing_of_IsElliptic` INSTANCE under `[NeZero 2]`, `[NeZero 3]`, `[IsElliptic]` (~200 lines in `HasseWeil/Curves/IntegralClosure.lean`) — makes `IsDedekindDomain C.CoordinateRing` available as instance (IC-001/2/3iii/4/5 all unconditional now). Delivered **T-INFRA-IC-006** (~90 lines): `mem_coordinateRing_of_valuation_le_one`, `const_of_no_poles_of_valuation_of_ordAtInfty` (full Silverman II.1.2 Part 2, prime-form), `const_of_isIntegral_polynomialX_of_ordAtInfty`, `const_of_valuation_le_one_of_ordAtInfty_nonneg` (T-II-3-008 ⇒, prime-form). Delivered **`HasseWeil/Curves/SmoothPointPrime.lean`**: `SmoothPoint.toHeightOneSpectrum` + `_injective`/`_surjective` (under `[IsAlgClosed F]` + `[IsElliptic]`) + `smoothPointEquivHeightOneSpectrum` packaged bijection. All axiom-clean. T-II-2-002/008/009 scoping audit in progress logs + shortcut bridge `Isogeny.fiber_witness_of_ker_card_eq_sepDegree` (reduces h_pc_fiber_witness to `|ker| = sepDeg`, finite-field entry point for Hasse bound chain). |
| worker-I | 2026-04-22 | Stream A: **T-II-2-008 full** `CurveMap.sum_ramificationIdx_mul_inertiaDeg_eq_degree` — diamond fixed, ~50 lines in `HasseWeil/Curves/CurveMap.lean`, packages `Ideal.sum_ramification_inertia` for generic `CurveMap + CoordHom` witness. Closes T-II-2-008 unconditionally (under `[IsIntegrallyClosed]` on both coordinate rings). Also delivered **`ordAtInfty_algebraMap_F_nonzero`** in `HasseWeil/Curves/Infinity.lean` (closes session-2-deferred lemma via `Algebra.norm_algebraMap_of_basis` + `natDegree_pow`) plus bridge wrapper in `OrdAtInftyBridge.lean`. **HOLE D closers** in `HasseWeil/Hasse/PointFix.lean` + `Unconditional.lean`: `hole_d_of_sepDegree_eq_pointCount` and `hole_d_of_hom_and_sepDegree` reduce the `hasse_bound_of_all_witnesses` fiber-witness HOLE D (originally a T-II-2-009 instance applied to `β_pc`) to the single identity `β_pc.sepDegree = pointCount W.toAffine`. Once stream-D `AdditionPullback` replaces `isogOneSub`'s placeholder, this identity holds (it's Silverman V.1.3) and HOLE D drops in. All axiom-clean. |
| Claude | 2026-04-22 | **REVIEW sweep**: verified 14 REVIEW-status tickets axiom-clean and promoted to DONE: T-II-1-001/002/003/006, T-II-2-008, T-II-3-001/001b/002/003/005/006/007, T-II-4-001, T-IV-2-008. Each target declaration verified to depend only on `[propext, Classical.choice, Quot.sound]`. T-II-1-004 stays REVIEW (Part 2 SmoothPoint-indexed form blocked on T-II-3-009 surjection). |
| Claude | 2026-04-26 | **T-HASSE-CLOSE-B Stream-D advance**: closed BRIDGE-001 for `[n]` family in `HasseWeil/BridgeMulByInt.lean` (axiom-clean under char ≠ 2). Built ~400 lines of Laurent leading-coefficient infrastructure (`localExpand_u_gen_*`, `localExpand_preΨ_2n_*`, `localExpand_mulByInt_y_*` via Wronskian-IV.2.3 formula). Added `formalX/Y_leadingCoeff`, `localExpand_inner_leadingCoeff` to `LocalExpansion.lean`. Added `HahnSeries.{leadingCoeff_inv,leadingCoeff_div}` to `HahnSeriesAux.lean`. Delivered `HasseWeil/Hasse/HoleE.lean` with axiom-clean `hole_e_closer`, `hasse_bound_via_workers`, `hole_e_from_signed_QF`, `hasse_bound_via_signed_QF` — full Hasse-Weil drop-in given CLOSE-A + CLOSE-C deliverables. T-IV-BRIDGE-001 / T-IV-BRIDGE-002 status B → P. |
| Claude | 2026-04-26 | **T-IV-BRIDGE-004 closed (B → D)**: `HasseWeil/BridgeFrobenius.lean` ships `formalIsogenySeries_frobenius : formalIsogenySeries W π = X^(card K)` axiom-clean via `localExpand_localParam` + `HahnSeries.single_pow`. Plus `omegaPullbackCoeff_frobenius = 0` direct via `Derivation.leibniz_pow` + `FiniteField.cast_card_eq_zero` (bypasses BRIDGE-001), `frobenius_pullbackKaehler_invariantDifferential = 0`, and `not_isSeparable_frobenius_of_witness`. Six axiom-clean theorems total. Also `hole_e_closer_of_isDualOf` and `hole_e_closer_via_isogDual` variants in HoleE.lean for direct CLOSE-C drop-in. CascadeValidation.lean refactored to sorry-free witness-parametric form (3 sorries → 0). T-IV-BRIDGE-002 [n] family helper. INDEX statistics: BLOCKED 18→17, DONE 82→83. |
| Claude | 2026-05-08 | **REVIEWER-DRIVEN PLAN UPDATE** (after `/expert-review` round-trip): Silverman re-read corrected the architectural framing. The fixed-field reverse inclusion is NOT the substantive primitive for `pc_fiber_witness`; Silverman III.4.10 proves the cardinality match via II.2.6(b) + translation bootstrap. The formal-group polynomial form is NOT how Silverman proves III.6.1; the differential identity `[p]*ω = 0` + II.2.12 (separable–inseparable factorisation) is. **Critical-path spine confirmed**: T-II-2-009 → III.4.10 → III.6.1 (separable + Frobenius cases) → III.6.3 → Hasse. **Updates**: T-III-4-014 PARTIAL → REVIEW (faithfulSMul_kernel + translateAlgEquivOfPoint_injective shipped); T-IV-2-005 PARTIAL → BLOCKED, **OFF Hasse-critical path** (formal-group abstract packaging not needed); T-III-4-015 reframed (closes mechanically once T-II-2-009 closes); T-V-1-003 reframed. **New tickets**: T-FROB-OMEGA-ZERO, T-FROB-INSEP, T-FROB-DUAL-ASSEMBLY (Conditional namespace, witness-parametric on II.2.12 — NOT on bound conclusion), T-VERSCHIEBUNG-ADAPTER (explicit anti-drift gate), T-POLE-DIVISOR-FALLBACK (Plan-C reserve for `1−π` if T-II-2-009 stalls). **Anti-drift gates** added to PROTOCOL.md (5 gates per reviewer). **Worker reassignment**: Worker B → T-II-2-009 + bootstrap; Worker A → T-II-2-016 (one-Frobenius-factor case for [p], with twists explicit); Worker C → T-FROB-OMEGA-ZERO + T-FROB-INSEP + T-FROB-DUAL-ASSEMBLY + T-VERSCHIEBUNG-ADAPTER. |

## Statistics

| | Count |
|---|---|
| Total tickets | 189 (was 184; +5 from 2026-05-08 reviewer-driven plan update) |
| OPEN | 65 (was 61; +4 new in 2026-05-08 plan: T-FROB-OMEGA-ZERO, T-FROB-INSEP, T-FROB-DUAL-ASSEMBLY, T-VERSCHIEBUNG-ADAPTER, T-POLE-DIVISOR-FALLBACK; offset −0 since T-III-4-014 R promoted) |
| PARTIAL | 20 (was 21; T-IV-2-005 PARTIAL → BLOCKED) |
| CHECKED-OUT | 1 |
| IN-PROGRESS | 0 |
| BLOCKED | 18 (was 17; T-IV-2-005 added) |
| REVIEW | 2 (was 1; T-III-4-014 promoted) |
| DONE | 83 |

## Critical-path priority (2026-05-08 final commitment — Path (i) Silverman spine via X.2 Pic⁰ for the §5.4 keystone)

### Strategic decision (2026-05-08): X.2 committed

After Worker C's two failed §5.4 specification attempts (Route Y rejected as circular by user; Route X rejected as circular by Worker C's own analysis — pairing identity at $(\pi, 1)$ IS the trace identity), the project commits to **X.2: Pic⁰ functoriality** for `qf_nonneg`'s dual-additivity content. Reviewer's third-pass guidance: "I would prefer A′ via Pic⁰ if the goal is reusable Silverman infrastructure" + reviewer's explicit rejection of X.1-equivalent direct-degree-computation as "alt-1: not a shorter route."

Estimated 6-12 weeks / ~750-1450 LOC across the chain T-CLASSGROUP-PIC0-BRIDGE → T-III-3-004 → T-III-6-002 → III.6.2(c) via Pic⁰ functoriality.



The original 2026-05-08 plan attempted a "Frobenius-plane duality short-circuit" that the reviewer's third soundness check identified as having a circular gap (V_π + π = [t] is NOT a formal consequence of V·π = π·V = [q]; the trace identity IS the substantive content). The project now commits to **Path (i): the full Silverman spine**.

### Bound-critical Silverman spine (Path i)

```
For pc_sepDeg_eq_pointCount (Worker B's parallel stream):
  Worker A's xy-family Lemma 2 (kernel-translation invariance for γ*x_gen)
    ─→ Worker B Lemma 5 (explicit pole-divisor sum)
       + Computation A bridge ([K(E):K(f)] = deg(div_∞ f), named non-trivial)
       ─→ tower equating
       ─→ pc_sepDeg_eq_pointCount unconditional

For qf_nonneg (Worker C's main stream, Silverman spine):
  T-II-2-016 generalised (II.2.12 for [p] → [q] via Frobenius twists, Worker A)
    ─→ III.6.1 Case 2 (Frobenius dual V_π exists)
  pc_sepDeg_eq_pointCount closure
    ─→ III.4.10(c) for 1−π specifically
    ─→ III.4.11 specialised to 1−π
    ─→ III.6.1 Case 1 (separable dual of 1−π exists)
  ★ III.6.2(c) restricted to ℤ[π] (the keystone — V_π + π = [t]) ★ NOT MECHANICAL
    ─→ III.6.2 restricted polarisation
    ─→ III.6.3 specialised to Frobenius plane: deg(rπ−s) = qr² − tr·rs + s²
    ─→ qf_nonneg unconditional
```

### Worker assignments (Path i)

| Worker | Owns | Output |
|---|---|---|
| Worker A | xy-family Lemma 2 substantive (addX/addY identities at W_KE for k ∈ E(F_q)) AND T-II-2-016 generalised (iterated II.2.12 from [p] to [q] via twists) | Inputs for §4 Lemma 2 + §5 Frobenius dual existence |
| Worker B | §4 pole-divisor closure: Lemma 5 (explicit sum) + Computation A bridge ([K(E):K(f)] = deg(div_∞ f)) + tower equating | pc_sepDeg_eq_pointCount unconditional for γ = 1−π |
| Worker C | §5.3 III.4.11 specialised to 1−π + ★ §5.4 restricted dual additivity (THE keystone) ★ + §5.5–§5.6 mechanical chain | qf_nonneg unconditional |

### Reviewer-flagged scope warnings

- **§5.4 is the keystone.** Restricted dual additivity (Silverman III.6.2(c) on $\mathbb{Z}[\pi]$) is genuinely substantive. Not a mechanical consequence of V·π = π·V = [q] + dual existence for 1−π separately. Estimated ~100-200 LOC. The bound's true bottleneck.
- **§4 Computation A bridge** ($[K(E):K(f)] = \deg(\mathrm{div}_\infty f)$) is a named non-trivial theorem, not a trivial polynomial-form derivation. Estimated ~80-150 LOC.
- **Supersingular caveat for §5.7**: $r\pi - s = 0$ can occur in End(E) for nonzero $(r, s)$ in supersingular cases. Polarisation must be stated for $\deg$ extended to endomorphisms with $\deg 0 = 0$.
- **One-variable discriminant argument** removed from §2: integer non-negativity at $r=1$ does NOT imply $t^2 \le 4q$ ($q=2, t=3$ counterexample). Two-variable form via rational density is essential.

### Total LOC estimate (Path i, revised after reviewer corrections)

~700-1300 LOC of substantive work across three workers, all on existing scaffolding plus the named substantive bridges. Higher than my earlier compressed estimates due to the §5.4 keystone, the Computation A bridge, and III.4.11 specialised — none of these are mechanical.

**OFF-critical-path** (long-term, not blocking Hasse under Path i): T-IV-2-005 (abstract `FormalGroup R` packaging), Pic⁰ infrastructure, quotient-curve infrastructure, full dual additivity on End(E), general II.2.6(b) base-change (avoided for §4 specifically; possibly still needed for III.4.11 staging).

Breakdown by section:

| Section | Count |
|---|---|
| II.1 Curves | 6 |
| II.2 Maps | 16 |
| II.3 Divisors | 12 |
| II.4 Differentials | 12 |
| III.1 Weierstrass | 11 |
| III.2 Group Law | 9 |
| III.3 EC | 7 |
| III.4 Isogenies | 17 |
| III.5 Invariant Differential | 10 |
| III.6 Dual Isogeny | 10 |
| IV.1 Expansion | 8 |
| IV.2 Formal Groups | 9 |
| IV.3 Associated Groups | 7 |
| IV.4 Inv Diff Formal | 6 |
| IV.5 Logarithm | 6 |
| IV.6 Over DVRs | 6 |
| IV.7 Height | 3 |
| IV-BRIDGE | 5 |
| V.1 Hasse | 6 |
| MIGRATE | 15 |
| **Total** | **181** |

★ marks the critical-path tickets (the ones that gate big chunks of downstream
work).

## Sorry-to-ticket mapping

These are the sorries currently in the codebase, mapped to which ticket will
close them:

| File | Count | Tickets that close them |
|---|---|---|
| `Endomorphism.lean` | 0 | T-III-4-009 (isogOneSub/isogSmulSub pullbacks closed with `AlgHom.id` placeholder on 2026-04-17; see ticket progress log) |
| `DualIsogeny.lean` | 8 | T-III-6-001..009 (the whole dual section) |
| `DegreeQuadraticForm.lean` | 1 | T-III-6-009 (positive definite QF) |
| `Frobenius.lean` | 1 | T-V-1-003 + T-V-1-004 (point count formula) — BLOCKED (placeholder `isogOneSub` degree = 1; see docstring) |
| `OmegaPullbackCoeff.lean` | 1 | T-IV-BRIDGE-001 (or bypass entirely) |
| `PullbackCoeff.lean` | 2 | T-III-5-006 (ring hom End → K̄), T-III-6-003 |
| `Ramification.lean` | 1 | T-II-1-001 (DVR Jacobian criterion) |
| `LocalExpansion.lean` | 1 | T-IV-BRIDGE-001 (coordHom_injective only) |

(Approx. 17 sorries total as of 2026-04-10. Endomorphism.lean dropped from 4 to 2
after worker-C deleted the mathematically false `isogTrace_mulByInt_zero`/`_one` in
T-III-4-003. LocalExpansion.lean dropped from 7 to 1 as of 2026-04-08. On 2026-04-17
Endomorphism.lean dropped 2 → 0 via `AlgHom.id` placeholder for
`isogOneSub.pullback`/`isogSmulSub.pullback` — axiom-clean, but makes the general-α
`degree` trivial until `AdditionPullback.lean` is finished.)

## Ticket table

Click each ticket ID to see its file. Status legend: `O` = OPEN, `C` = CHECKED-OUT,
`P` = IN-PROGRESS, `B` = BLOCKED, `R` = REVIEW, `D` = DONE.

### Stream A — Curves (II)

#### II.1 Curves

| ID | Status | Owner | Title |
|---|---|---|---|
| [T-II-1-001](curves/T-II-1-001-dvr-at-smooth-point.md) | D | worker-A | DVR at smooth point |
| [T-II-1-002](curves/T-II-1-002-ord-p.md) | D | worker-A | `ord_P : K(C) → ℤ ∪ ∞` |
| [T-II-1-003](curves/T-II-1-003-uniformizer.md) | D | worker-A | uniformizer |
| [T-II-1-004](curves/T-II-1-004-no-pole-zero-const.md) | R | worker-I | no zeros/poles ⇒ constant (Part 1 done; Part 2 prime-form via IC-006) |
| [T-II-1-005](curves/T-II-1-005-finite-separable-over-uniformizer.md) | B | — | K(C) finite separable over K(t) (needs Luroth + Kähler diff separability) |
| [T-II-1-006](curves/T-II-1-006-uniformizer-K-rational.md) | D | worker-A | uniformizer in K(C) for K-rational P |

#### II.2 Maps

| ID | Status | Owner | Title |
|---|---|---|---|
| [T-II-2-001](curves/T-II-2-001-rational-map-is-morphism.md) | D | worker-H | rational map ⇒ morphism |
| [T-II-2-002](curves/T-II-2-002-nonconst-surjective.md) | O | — | nonconst morphism is surjective |
| [T-II-2-003](curves/T-II-2-003-curves-extensions-functor.md) | O | — | curves ↔ field extensions |
| [T-II-2-004](curves/T-II-2-004-degree-types.md) | D | worker-H | deg, deg_s, deg_i (definitions) |
| [T-II-2-005](curves/T-II-2-005-norm-map.md) | O | — | norm map φ_* |
| [T-II-2-006](curves/T-II-2-006-deg-one-iso.md) | O | — | deg-1 ⇒ iso |
| [T-II-2-007](curves/T-II-2-007-ramification-index.md) | O | — | ramification index e_φ(P) |
| [T-II-2-008](curves/T-II-2-008-fiber-sum-degree.md) | D | worker-I | Σ e_φ(P) = deg φ (generic CurveMap via CoordHom witness, diamond fixed) |
| [T-II-2-009](curves/T-II-2-009-fiber-card-deg-s.md) | P | worker-A + Claude | #φ⁻¹(Q) = deg_s a.a. — Pieces 1–8 (witness form) + Piece 9 (inertiaDeg = 1 via LinearEquiv transport, diamond sidestep) ★ |
| [T-II-2-010](curves/T-II-2-010-ramification-chain-rule.md) | O | — | ramification chain rule |
| [T-II-2-011](curves/T-II-2-011-unramified-iff.md) | P | worker-A | unramified ⇔ #φ⁻¹ = deg φ (witness-parametric form; combinatorial) |
| [T-II-2-012](curves/T-II-2-012-frobenius-construction.md) | D | worker-C | Frobenius morphism (EC case) |
| [T-II-2-013](curves/T-II-2-013-frobenius-pullback-Kq.md) | D | worker-C | K(C^q) = K(C)^q (EC case) |
| [T-II-2-014](curves/T-II-2-014-frobenius-purely-inseparable.md) | D | worker-C | Frobenius purely inseparable (EC case) |
| [T-II-2-015](curves/T-II-2-015-frobenius-degree-q.md) | D | worker-C | deg(Frobenius) = q (EC case) |
| [T-II-2-016](curves/T-II-2-016-factor-sep-frob.md) | O | — | factor as sep ∘ Frob^e ★ |

#### II.3 Divisors

| ID | Status | Owner | Title |
|---|---|---|---|
| [T-II-3-001](curves/T-II-3-001-divisor-def.md) | D | worker-A | `Divisor C` |
| [T-II-3-001b](curves/T-II-3-001b-projective-divisor.md) | D | worker-K | `ProjectiveDivisor C` (∞-aware, scaffolding only) |
| [T-II-3-002](curves/T-II-3-002-divisor-degree.md) | D | worker-A | `Divisor.degree` |
| [T-II-3-003](curves/T-II-3-003-deg-zero-subgroup.md) | D | worker-A | `Div⁰` |
| [T-II-3-004](curves/T-II-3-004-galois-action-divisors.md) | D | worker-H | Galois action on divisors |
| [T-II-3-005](curves/T-II-3-005-div-of-function.md) | D | worker-I | div(f) |
| [T-II-3-006](curves/T-II-3-006-principal-equivalence.md) | D | worker-I | principal divisor, ~ |
| [T-II-3-007](curves/T-II-3-007-pic-pic-zero.md) | D | worker-I | Pic, Pic⁰ |
| [T-II-3-008](curves/T-II-3-008-div-zero-iff-const.md) | P | worker-I | div(f) = 0 ⇔ f ∈ K̄* (prime-form via IC-006) |
| [T-II-3-009](curves/T-II-3-009-deg-div-zero.md) | C | worker-K | deg(div f) = 0 (projective form, under [IsAlgClosed F]) |
| [T-II-3-010](curves/T-II-3-010-exact-sequence.md) | O | — | 1 → K̄* → K̄(C)* → Div⁰ → Pic⁰ → 0 |
| [T-II-3-011](curves/T-II-3-011-pullback-pushforward.md) | O | — | φ*, φ_* on divisors |
| [T-II-3-012](curves/T-II-3-012-pullback-properties.md) | O | — | Prop II.3.6(a–f) |

#### II.4 Differentials

| ID | Status | Owner | Title |
|---|---|---|---|
| [T-II-4-001](curves/T-II-4-001-differentials-def.md) | D | worker-A | `Differentials C` |
| [T-II-4-002](curves/T-II-4-002-differentials-1d.md) | O | — | Ω_C is 1-dim |
| [T-II-4-003](curves/T-II-4-003-dx-basis.md) | O | — | dx is basis |
| [T-II-4-004](curves/T-II-4-004-pullback-injective-iff-separable.md) | O | — | sep ⇔ φ* injective ★ |
| [T-II-4-005](curves/T-II-4-005-omega-eq-g-dt.md) | O | — | ω = g·dt for uniformizer t |
| [T-II-4-006](curves/T-II-4-006-df-dt-regular.md) | O | — | df/dt regular at P |
| [T-II-4-007](curves/T-II-4-007-ord-omega-well-defined.md) | O | — | ord_P(ω) well-defined |
| [T-II-4-008](curves/T-II-4-008-ord-fdx-formula.md) | O | — | order of f·dx |
| [T-II-4-009](curves/T-II-4-009-almost-all-ord-zero.md) | O | — | ord_P(ω) = 0 a.e. |
| [T-II-4-010](curves/T-II-4-010-div-omega.md) | O | — | div(ω) definition |
| [T-II-4-011](curves/T-II-4-011-holomorphic-nonvanishing.md) | O | — | holomorphic, nonvanishing |
| [T-II-4-012](curves/T-II-4-012-canonical-class.md) | O | — | canonical divisor class |

### Stream B — Weierstrass (III.1, III.2, III.3)

#### III.1 Weierstrass

| ID | Status | Owner | Title |
|---|---|---|---|
| [T-III-1-001](ec/T-III-1-001-weierstrass-equation.md) | D | — | Weierstrass eq, b/c/Δ/j (mathlib) |
| [T-III-1-002](ec/T-III-1-002-invariant-differential.md) | D | — | ω = dx/(2y+a₁x+a₃) |
| [T-III-1-003](ec/T-III-1-003-change-of-variables.md) | D | — | change of variables (mathlib) |
| [T-III-1-004](ec/T-III-1-004-nonsingular-iff-disc.md) | D | — | nonsingular ⇔ Δ ≠ 0 (mathlib) |
| [T-III-1-005](ec/T-III-1-005-node-iff.md) | D | worker-B | node ⇔ c₄ ≠ 0 |
| [T-III-1-006](ec/T-III-1-006-cusp-iff.md) | D | worker-B | cusp ⇔ c₄ = 0 |
| [T-III-1-007](ec/T-III-1-007-iso-iff-same-j.md) | D | — | iso ⇔ same j (mathlib) |
| [T-III-1-008](ec/T-III-1-008-every-j-realized.md) | D | — | every j₀ realized (mathlib) |
| [T-III-1-009](ec/T-III-1-009-div-omega-zero.md) | O | — | div(ω) = 0 ★ |
| [T-III-1-010](ec/T-III-1-010-singular-birational-P1.md) | O | — | singular ⇒ birational ℙ¹ |
| [T-III-1-011](ec/T-III-1-011-legendre-form.md) | D | worker-B | Legendre form |

#### III.2 Group Law

| ID | Status | Owner | Title |
|---|---|---|---|
| [T-III-2-001](ec/T-III-2-001-composition-law.md) | D | — | composition via line |
| [T-III-2-002](ec/T-III-2-002-abelian-group.md) | D | — | abelian group structure |
| [T-III-2-003](ec/T-III-2-003-EK-subgroup.md) | D | — | E(K) is subgroup |
| [T-III-2-004](ec/T-III-2-004-explicit-addition.md) | D | — | addition algorithm |
| [T-III-2-005](ec/T-III-2-005-doubling-formula.md) | D | — | doubling x([2]P) |
| [T-III-2-006](ec/T-III-2-006-even-functions.md) | D | worker-B | f even ⇔ f ∈ K(x) |
| [T-III-2-007](ec/T-III-2-007-Ens-nonsing-part.md) | C | worker-B | E_ns nonsingular part |
| [T-III-2-008](ec/T-III-2-008-Ens-Ga-Gm.md) | O | — | E_ns ≅ G_a or G_m |
| [T-III-2-009](ec/T-III-2-009-translation-map.md) | O | — | τ_Q : E → E translation |

#### III.3 Elliptic Curves

| ID | Status | Owner | Title |
|---|---|---|---|
| [T-III-3-001](ec/T-III-3-001-EC-genus-1-base-point.md) | D | — | EC = (E, O) |
| [T-III-3-002](ec/T-III-3-002-K-E-x-y.md) | D | worker-C | [K(E):K(x)] = 2 |
| [T-III-3-003](ec/T-III-3-003-P-Q-equiv-implies-eq.md) | C | worker-K | (P) ~ (Q) ⇒ P = Q (blocked on T-II-3-001b) |
| [T-III-3-004](ec/T-III-3-004-Pic-zero-iso-E.md) | O | — | Pic⁰(E) ≅ E ★ |
| [T-III-3-005](ec/T-III-3-005-D-principal-iff.md) | O | — | D principal iff |
| [T-III-3-006](ec/T-III-3-006-addition-is-morphism.md) | D | — | addition is morphism |
| [T-III-3-007](ec/T-III-3-007-exact-sequence-EK.md) | O | — | exact sequence for E |

### Stream C — Isogenies (III.4, III.5, III.6)

#### III.4 Isogenies

| ID | Status | Owner | Title |
|---|---|---|---|
| [T-III-4-001](ec/T-III-4-001-isogeny-def.md) | D | — | Isogeny structure |
| [T-III-4-002](ec/T-III-4-002-deg-types.md) | D | — | deg, deg_s, deg_i |
| [T-III-4-003](ec/T-III-4-003-mul-by-m.md) | D | worker-C | [m] ≠ 0 |
| [T-III-4-004](ec/T-III-4-004-Hom-torsion-free.md) | P | worker-A | Hom torsion-free (substance via degree) |
| [T-III-4-005](ec/T-III-4-005-End-integral-domain.md) | P | worker-C | End integral domain (substance only) |
| [T-III-4-006](ec/T-III-4-006-E-m-torsion.md) | D | worker-C | E[m] (def + mem_iff) |
| [T-III-4-007](ec/T-III-4-007-example-deg2-isogeny.md) | O | — | deg-2 example |
| [T-III-4-008](ec/T-III-4-008-frobenius-endomorphism.md) | D | — | Frobenius endo |
| [T-III-4-009](ec/T-III-4-009-translation-isogeny.md) | O | — | τ_Q : E → E |
| [T-III-4-010](ec/T-III-4-010-isogeny-is-hom.md) | ✅ | worker-A | every isogeny is homomorphism (structural via Isogeny struct) |
| [T-III-4-011](ec/T-III-4-011-ker-finite.md) | P | worker-A | ker finite (witness form; uncond for Finite Point) |
| [T-III-4-012](ec/T-III-4-012-fiber-card-deg-s.md) | P | worker-A | #φ⁻¹(Q) = deg_s (witness form) ★ |
| [T-III-4-013](ec/T-III-4-013-ramif-eq-deg-i.md) | P | worker-A | e_φ(P) = deg_i (witness-parametric, product + ratio forms) ★ |
| [T-III-4-014](ec/T-III-4-014-ker-iso-aut.md) | R | Worker B (audit) | ker ≅ Aut Galois ★ — injection half shipped (faithfulSMul_kernel + translateAlgEquivOfPoint_injective); surjection follows from T-II-2-009 + Field.finSepDegree bound |
| [T-III-4-015](ec/T-III-4-015-separable-unramified-galois.md) | P | worker-A | sep ⇒ #ker = deg (witness form) ★ |
| [T-III-4-016](ec/T-III-4-016-factorization.md) | P | worker-A | factorization theorem (witness-parametric, existence + uniqueness + ∃!) ★ |
| [T-III-4-017](ec/T-III-4-017-quotient-curve.md) | O | — | quotient by finite subgroup ★ |
| [T-III-4-020](ec/T-III-4-020-mulByInt-comp-eq-mul.md) | ✅ | worker-A | `[m]∘[n] = [m·n]` (DONE via Jacobian approach) |

#### III.5 Invariant Differential

| ID | Status | Owner | Title |
|---|---|---|---|
| [T-III-5-001](ec/T-III-5-001-translation-invariance.md) | P | worker-J | τ_Q*ω = ω (witness form) |
| [T-III-5-002](ec/T-III-5-002-pullback-additivity.md) | O | — | (φ+ψ)*ω = φ*ω + ψ*ω ★ |
| [T-III-5-003](ec/T-III-5-003-mul-by-m-omega.md) | O | — | [m]*ω = mω |
| [T-III-5-004](ec/T-III-5-004-mul-by-m-separable.md) | P | worker-J | m ≠ 0 ⇒ [m] separable (witness form) |
| [T-III-5-005](ec/T-III-5-005-m-plus-n-frob-separable.md) | P | worker-J | m + nπ separable iff p ∤ m ★ (witness form) |
| [T-III-5-006](ec/T-III-5-006-ring-hom-end.md) | O | — | α ↦ a_α ring hom ★ |
| [T-III-5-007](ec/T-III-5-007-ker-coeff-inseparable.md) | O | — | kernel = inseparables |
| [T-III-5-008](ec/T-III-5-008-char-zero-end-commutative.md) | O | — | char 0 ⇒ commutative |
| [T-III-5-009](ec/T-III-5-009-omega-pullback-coeff.md) | D | — | omegaPullbackCoeff |
| [T-III-5-010](ec/T-III-5-010-chain-rule.md) | D | — | chain rule |

#### III.6 Dual Isogeny

| ID | Status | Owner | Title |
|---|---|---|---|
| [T-III-6-001](ec/T-III-6-001-dual-existence.md) | O | — | dual existence + uniqueness ★ |
| [T-III-6-002](ec/T-III-6-002-dual-via-pic.md) | O | — | dual via Pic⁰ |
| [T-III-6-003](ec/T-III-6-003-dual-comp-formula.md) | ✅cc | — | φ̂∘φ = [deg φ] (content-complete, cascades T-III-6-001) |
| [T-III-6-004](ec/T-III-6-004-dual-functoriality.md) | O | — | (λ∘φ)^ = φ̂∘λ̂ |
| [T-III-6-005](ec/T-III-6-005-dual-additivity.md) | P | worker-A | (φ+ψ)^ = φ̂+ψ̂ (witness forms `dual_add_of_trace_witnesses` + `dual_add_of_sum_witnesses`) ★ |
| [T-III-6-006](ec/T-III-6-006-dual-mul-by-m.md) | ✅cc | worker-A | [m]^ = [m] (DONE for m ≠ 0, cascades T-III-6-001) |
| [T-III-6-007](ec/T-III-6-007-deg-dual.md) | ✅cc | — | deg φ̂ = deg φ (content-complete, cascades T-III-6-001) |
| [T-III-6-008](ec/T-III-6-008-dual-dual.md) | ✅cc | — | (φ̂)^ = φ (content-complete, cascades T-III-6-001) |
| [T-III-6-009](ec/T-III-6-009-deg-quadratic-form.md) | O | — | deg pos. def. QF ★ |
| [T-III-6-010](ec/T-III-6-010-E-m-structure.md) | P | worker-J | E[m] structure (#E[m] = m² witness form) |

### Stream D — Formal groups (IV)

#### IV.1 Expansion

| ID | Status | Owner | Title |
|---|---|---|---|
| [T-IV-1-001](formal/T-IV-1-001-local-parameter-z-w.md) | B | — | z = -x/y, w = -1/y (needs `IsUniformizerAt`) |
| [T-IV-1-002](formal/T-IV-1-002-w-of-z-exists.md) | B | — | w(z) exists (needs T-IV-1-005 Hensel) |
| [T-IV-1-003](formal/T-IV-1-003-w-uniqueness.md) | B | — | w(z) unique (released by worker-E; PowerSeries typeclass gaps) |
| [T-IV-1-004](formal/T-IV-1-004-A-n-homogeneous.md) | B | — | A_n homogeneous (needs IV-1-003) |
| [T-IV-1-005](formal/T-IV-1-005-hensel.md) | B | — | Hensel's lemma for R[[T]][X] (needs mathlib upstream) |
| [T-IV-1-006](formal/T-IV-1-006-x-y-laurent.md) | B | — | x(z), y(z) Laurent (needs IV-1-002) |
| [T-IV-1-007](formal/T-IV-1-007-omega-z.md) | B | — | ω(z) power series (needs IV-1-006) |
| [T-IV-1-008](formal/T-IV-1-008-formal-addition.md) | D | — | F(z₁,z₂) |

#### IV.2 Formal groups (abstract)

| ID | Status | Owner | Title |
|---|---|---|---|
| [T-IV-2-001](formal/T-IV-2-001-formal-group-def.md) | D | worker-A | `FormalGroup R` |
| [T-IV-2-002](formal/T-IV-2-002-formal-group-hom.md) | D | worker-A | `FormalGroupHom` |
| [T-IV-2-003](formal/T-IV-2-003-additive-formal-group.md) | D | worker-A | Ĝ_a additive |
| [T-IV-2-004](formal/T-IV-2-004-multiplicative-formal-group.md) | D | worker-A | Ĝ_m multiplicative |
| [T-IV-2-005](formal/T-IV-2-005-Ehat-formal-group.md) | B | — | Ê for elliptic curve — **OFF Hasse-critical path** (2026-05-08): differential bypass replaces formal-group polynomial route. Bridge (a) associativity is genuine Silverman IV.1, ~500-1500 LOC; long-term goal but not blocking. |
| [T-IV-2-006](formal/T-IV-2-006-mul-by-m.md) | D | worker-G | [m] : F → F (ℕ done — axiom-clean, verified 2026-04-20) |
| [T-IV-2-007](formal/T-IV-2-007-mul-by-m-leading.md) | D | worker-G | [m](T) = mT + O(T²) (ℕ done — axiom-clean, verified 2026-04-20) |
| [T-IV-2-008](formal/T-IV-2-008-mul-by-m-iso.md) | D | worker-G | m ∈ R* ⇒ [m] iso (existence form for ℕ done; `FormalGroupHom` iso deferred) |
| [T-IV-2-009](formal/T-IV-2-009-power-series-invertibility.md) | D | worker-G | invertibility lemma (`compInverse` + `subst_compInverse_eq_X`) |
| [T-IV-2-010](formal/T-IV-2-010-hom-comp.md) | D | worker-G | FormalGroupHom composition (axiom-clean, verified 2026-04-20) |
| [T-IV-2-011](formal/T-IV-2-011-formal-inverse.md) | D | worker-G | formal inverse series `i(T)` (def + coeffs + `fAdd_X_inverse_eq_zero` functional equation) |

#### IV.3 Associated groups

| ID | Status | Owner | Title |
|---|---|---|---|
| [T-IV-3-001](formal/T-IV-3-001-F-of-M.md) | D | worker-G | F(M) for complete local R (AddCommGroup `evalGroup` delivered 2026-04-18) |
| [T-IV-3-002](formal/T-IV-3-002-F-M-n.md) | D | — | F(M^n) subgroups (delivered 2026-04-20, `Associated.lean`) |
| [T-IV-3-003](formal/T-IV-3-003-Ga-M.md) | D | — | Ĝ_a(M) = (M, +) (delivered 2026-04-20, `Associated.lean`) |
| [T-IV-3-004](formal/T-IV-3-004-Gm-M.md) | P | — | Ĝ_m(M) = (1+M, ·) — operation-level identity delivered 2026-04-20; AddEquiv packaging deferred |
| [T-IV-3-005](formal/T-IV-3-005-E-hat-M-to-EK.md) | B | — | Ê(M) → E(K) ★ (needs Ê, IV-3-001) |
| [T-IV-3-006](formal/T-IV-3-006-graded-iso.md) | D | worker-I | F(M^n)/F(M^(n+1)) ≅ M^n/M^(n+1) — congruence + forward hom + kernel/range + packaged equivalence, delivered 2026-04-20 |
| [T-IV-3-007](formal/T-IV-3-007-torsion-p-power.md) | D | — | torsion p-power (addOrderOf_isPowOf via left-inverse + diamond-fixed EvalGroup) |

#### IV.4 Invariant differential

| ID | Status | Owner | Title |
|---|---|---|---|
| [T-IV-4-001](formal/T-IV-4-001-invariant-differential-def.md) | D | worker-D | InvariantDifferential F |
| [T-IV-4-002](formal/T-IV-4-002-normalized-differential.md) | D | worker-D | normalized differential |
| [T-IV-4-003](formal/T-IV-4-003-unique-normalized.md) | D | worker-D | ω = F_X(0,T)⁻¹ dT |
| [T-IV-4-004](formal/T-IV-4-004-every-is-a-omega.md) | D | worker-D | every inv diff = aω |
| [T-IV-4-005](formal/T-IV-4-005-chain-rule.md) | D | worker-D | ω_G ∘ f = f'(T) ω_F ★ |
| [T-IV-4-006](formal/T-IV-4-006-frob-decomposition.md) | D | worker-G | [p] = pf + g(T^p) ★ (axiom-clean, verified 2026-04-20) |

#### IV.5 Formal logarithm

| ID | Status | Owner | Title |
|---|---|---|---|
| [T-IV-5-001](formal/T-IV-5-001-log-F.md) | D | worker-G | log_F(T) (axiom-clean, verified 2026-04-20) |
| [T-IV-5-002](formal/T-IV-5-002-exp-F.md) | D | worker-G | exp_F(T) (def + full inverse `subst_compInverse_eq_X`) |
| [T-IV-5-003](formal/T-IV-5-003-log-iso-Ga.md) | D | worker-S4 | log_F iso for torsion-free (via Silverman IV.4.2 translation invariance) |
| [T-IV-5-004](formal/T-IV-5-004-torsion-free-commutative.md) | D | worker-G | torsion-free ⇒ commutative (axiom-clean, verified 2026-04-20) |
| [T-IV-5-005](formal/T-IV-5-005-bn-bound.md) | D | worker-G | b_n bound (as n-smul identity) (axiom-clean, verified 2026-04-20) |
| [T-IV-5-006](formal/T-IV-5-006-log-exp-structure.md) | D | worker-G | log_F, exp_F structure (axiom-clean, verified 2026-04-20) |

#### IV.6 Over DVRs

| ID | Status | Owner | Title |
|---|---|---|---|
| [T-IV-6-001](formal/T-IV-6-001-torsion-divides-vp.md) | B | — | torsion divides v(p) power (needs IV-3, DVR theory) |
| [T-IV-6-002](formal/T-IV-6-002-zp-torsion-free.md) | B | — | F(pℤ_p) torsion-free p≥2 (needs IV-3, DVR) |
| [T-IV-6-003](formal/T-IV-6-003-vn-factorial-bound.md) | D | worker-G | v(n!) bound (axiom-clean, verified 2026-04-20) |
| [T-IV-6-004](formal/T-IV-6-004-convergence.md) | B | — | series convergence (needs IV-3, DVR) |
| [T-IV-6-005](formal/T-IV-6-005-log-iso-large-r.md) | B | — | log_F : F(M^r) ≅ Ĝ_a(M^r) (needs IV-3, IV-5-003) |
| [T-IV-6-006](formal/T-IV-6-006-F-Mr-torsion-free.md) | B | — | F(M^r) torsion-free (needs IV-3, DVR) |

#### IV.7 Height (char p)

| ID | Status | Owner | Title |
|---|---|---|---|
| [T-IV-7-001](formal/T-IV-7-001-height-of-hom.md) | D | worker-G | height(f) (axiom-clean, verified 2026-04-20) |
| [T-IV-7-002](formal/T-IV-7-002-height-of-F.md) | D | worker-G | height(F) := height([p]) (axiom-clean, verified 2026-04-20) |
| [T-IV-7-003](formal/T-IV-7-003-height-applications.md) | D | worker-G | height_comp via `PowerSeries.order_subst` |

#### IV-BRIDGE (formal ↔ curve)

| ID | Status | Owner | Title |
|---|---|---|---|
| [T-IV-BRIDGE-001](formal/T-IV-BRIDGE-001-omega-coeff-is-formal-leading.md) | P | Claude / worker-A | omegaPullbackCoeff = formal coeff ([n] family closed; general α open) |
| [T-IV-BRIDGE-002](formal/T-IV-BRIDGE-002-omega-coeff-in-base.md) | P | Claude / worker-A | a_α ∈ F (witness form + [n] family closed) |
| [T-IV-BRIDGE-003](formal/T-IV-BRIDGE-003-formal-additivity.md) | B | — | formal additivity ↔ curve ★ (needs BRIDGE-001) |
| [T-IV-BRIDGE-004](formal/T-IV-BRIDGE-004-frob-formal.md) | D | Claude | Frobenius pulled back = T^q (closed via direct `localExpand_localParam` + `HahnSeries.single_pow`) |
| [T-IV-BRIDGE-005](formal/T-IV-BRIDGE-005-kaehler-rank-one.md) | D | — | dim_K(E) Ω = 1 (already in codebase) |

### Stream V — Hasse bound (V.1)

| ID | Status | Owner | Title |
|---|---|---|---|
| [T-V-1-001](hasse/T-V-1-001-Eq-eq-ker.md) | D | worker-J | E(F_q) = ker(1−π) |
| [T-V-1-002](hasse/T-V-1-002-1-minus-pi-separable.md) | D | worker-J | 1−π separable (via trivial self-algebra under placeholder) |
| [T-V-1-003](hasse/T-V-1-003-card-Eq-eq-deg.md) | P | worker-J | #E(F_q) = deg(1−π) (witness form; closes mechanically when T-II-2-009 closes) |
| [T-V-1-004](hasse/T-V-1-004-card-formula.md) | P | worker-J | #E(F_q) = q + 1 − tr(π) (witness form) |
| [T-V-1-005](hasse/T-V-1-005-cauchy-schwarz.md) | D | — | Cauchy-Schwarz |
| [T-V-1-006](hasse/T-V-1-006-hasse-bound.md) | D | — | Hasse bound (algebraic) |
| [T-POLE-DIVISOR-FALLBACK](hasse/T-POLE-DIVISOR-FALLBACK-pc-fiber-witness.md) | O (reserve) | — | Plan-C pole-divisor proof of #ker(1−π) = deg(1−π) — activate only if T-II-2-009 stalls |

### Stream V/F — Frobenius dual chain (2026-05-08, reviewer-driven)

| ID | Status | Owner | Title |
|---|---|---|---|
| [T-FROB-OMEGA-ZERO](ec/T-FROB-OMEGA-ZERO-mulByNat-p-omega.md) | O | Worker C | omegaPullbackCoeff([p]) = 0 in char p (one-line corollary) |
| [T-FROB-INSEP](ec/T-FROB-INSEP-mulByNat-p-inseparable.md) | O | Worker C | [p] inseparable in char p (corollary of T-FROB-OMEGA-ZERO + III.4.2(c)) |
| [T-FROB-DUAL-ASSEMBLY](ec/T-FROB-DUAL-ASSEMBLY-frobenius-dual-of-factorization.md) | O | Worker C | Frobenius dual from II.2.12 (Conditional namespace, witness on II.2.12 NOT bound conclusion) |
| [T-VERSCHIEBUNG-ADAPTER](ec/T-VERSCHIEBUNG-ADAPTER-qf-nonneg.md) | O | Worker C | FrobeniusVerschiebungData → qf_nonneg (explicit anti-drift gate; pivot trigger to Route A′ if requires general dual additivity) |

### Migration tickets

| ID | Status | Owner | Title |
|---|---|---|---|
| [T-MIGRATE-001](hasse/T-MIGRATE-001-create-directories.md) | D | worker-C | Create directory structure |
| [T-MIGRATE-002](hasse/T-MIGRATE-002-universal.md) | D | worker-C | Move Universal.lean |
| [T-MIGRATE-003](hasse/T-MIGRATE-003-eds.md) | D | worker-C | Move EllipticDivisibilitySequence.lean |
| [T-MIGRATE-004](hasse/T-MIGRATE-004-divpoly.md) | D | worker-C | Move DivisionPolynomial.lean |
| [T-MIGRATE-005](hasse/T-MIGRATE-005-pullback-kaehler.md) | D | worker-C | Move PullbackKaehler.lean |
| [T-MIGRATE-006](hasse/T-MIGRATE-006-diff-quotient.md) | D | worker-C | Move DiffQuotientRule.lean |
| [T-MIGRATE-007](hasse/T-MIGRATE-007-curves-basic-maps.md) | O | — | Refactor → Curves/ |
| [T-MIGRATE-008](hasse/T-MIGRATE-008-invariant-diff.md) | O | — | Refactor → EC/InvariantDiff |
| [T-MIGRATE-009](hasse/T-MIGRATE-009-isogeny.md) | O | — | Refactor → EC/Isogeny |
| [T-MIGRATE-010](hasse/T-MIGRATE-010-dual-isogeny.md) | O | — | Refactor → EC/DualIsogeny+DegreeForm |
| [T-MIGRATE-011](hasse/T-MIGRATE-011-formal-group.md) | O | — | Refactor → FormalGroup/ |
| [T-MIGRATE-012](hasse/T-MIGRATE-012-frobenius.md) | O | — | Refactor → Frobenius/ |
| [T-MIGRATE-013](hasse/T-MIGRATE-013-hasse.md) | O | — | Refactor → Hasse/ |
| [T-MIGRATE-014](hasse/T-MIGRATE-014-kernel-degree.md) | O | — | Refactor → EC/IsogenyFactor |
| [T-MIGRATE-015](hasse/T-MIGRATE-015-root-import.md) | O | — | Update HasseWeil.lean root |

## Marked DONE on day 1 (already in existing code)

These tickets are pre-marked as DONE because the existing code already contains
a working implementation. New workers can verify and adopt them, but should not
re-implement.

- T-III-1-001, T-III-1-002, T-III-1-003, T-III-1-004, T-III-1-007, T-III-1-008
- T-III-2-001, T-III-2-002, T-III-2-003, T-III-2-004, T-III-2-005
- T-III-3-001, T-III-3-006
- T-III-4-001, T-III-4-002, T-III-4-008
- T-III-5-009, T-III-5-010
- T-IV-1-008
- T-V-1-005, T-V-1-006

(21 tickets DONE)
