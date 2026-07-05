# Ticket Board — ModularCurves (Phase 1–2)

*/develop 1g, 2026-07-05. Statements are canonical in the Lean skeleton (commit
`b758179b`): every proof ticket is "discharge the `sorry` at the named declaration" —
the signature in the file is the contract (develop.md §2.5). No ticket may alter a
statement; a worker convinced a statement is wrong hard-stops with a B2 report
(`b2_log.jsonl`) and the board is replanned.*

**Standing rules for every ticket**
1. Before starting: complete the leaf's ≥3-attack adversarial block in
   `decomposition.md` (several are marked *partial*).
2. `sorry`s outside your target may be *used* (they are WIP markers), but the DATA-SORRY
   register in `plan.md` is frozen: no new data-sorries; consume registered data only
   through its specification theorems.
3. Done bar: `lake build` green; your declaration sorry-free; `#print axioms` on it
   shows only `propext`/`Classical.choice`/`Quot.sound` + `sorryAx` inherited from
   *registered* dependencies (list them in the closing note); **no `set_option
   maxHeartbeats` anywhere** (needing one ⟹ file a `/decompose-proof` ticket instead).
4. PENDING-SOURCE(KM) tickets (marked ⧗KM) may be *worked for statements and
   non-KM-sourced lemmas* but not closed until the full KM text lands and the verbatim
   quote-gate in `decomposition.md` is satisfied.

## Summary
- Work tickets: 24 · Cleanup tickets: 11 · Milestones: T-E2, T-E7, T-E9, T-F4
- Parallel capacity: **5 lanes** (A, B, C, D, E/F) after T-A5; within lanes see
  `Parallel` fields. Start-now set: **T-E1, T-E2, T-A2, T-B2, T-D3, T-F0** (6 workers).

## Streams
- **A** foundations (EllipticCurve/*) — blocks B, C, D at *proof* level only
  (statements are frozen; other lanes may start on their non-DS2-dependent parts).
- **B** torsion & μ_N (Torsion, MuN) — B2/B3 independent of A-proofs.
- **C** Weil pairing (WeilPairing/*) — construction ⧗KM; comparison ticket ready.
- **D** Drinfeld structures (LevelStructure/*) — KM Ch. 1 fully sourced.
- **E** moduli + representability (Moduli/*) — E1/E2 ring-level, independent of ALL
  scheme-level lanes.
- **F** Y(ρ,p) (ModularCurve/YRho) — F0 now; F1 after AG-GG scoping; F4 phase 3.

---

### [T-E1] Tate normal form (ring level) — PROVABLE NOW
- **Status**: open · **File**: Moduli/Representability.lean ·
  `exists_unique_variableChange_isTateNormal`
- **Depends on**: none · **Parallel**: yes · **Type**: theorem
- **Statement**: in skeleton (∃! `vc : VariableChange R`, `(vc • W).IsTateNormal ∧
  vc.r = x ∧ vc.t = y`, given `W.IsElliptic`, `Equation x y`, `NowhereOrderLEThree`).
- **Proof sketch** (Loeffler Prop 3.3.4, proof p. 14, in hand):
  1. Translate `(x,y) → (0,0)`: apply `vc₁ = ⟨1, x, 0, y⟩`; mathlib
     `VariableChange` action lemmas compute the new `a₆ = 0`-form.
  2. Not-2-torsion ⟹ `ψ₂(0,0) = 2y' + a₁x' + a₃ = a₃`-unit reasoning: tangent slope
     defined; shear `y ↦ y + rx` to make the tangent at origin the line `y = 0`
     (kills `a₄`).
  3. Not-3-torsion ⟹ origin not inflexion ⟹ `a₂` unit; scale `x ↦ u²x, y ↦ u³y` with
     `u = a₂/a₃`-normalisation to reach `a₂ = a₃`.
  4. Uniqueness: compare coefficients of the two Tate-normal forms under a general
     `VariableChange` fixing `(0,0)` (forces `u = 1, r = s = t = 0`).
  5. Unit-hypothesis bookkeeping: `IsUnit (ψ₂ψ₃-eval)` ⟹ each intermediate divisor is a
     unit (localisation-free — everything is literal ring algebra).
- **Mathlib needed**: `WeierstrassCurve.VariableChange` group action (`vc • W`),
  `WeierstrassCurve.Ψ` + `evalEval` (verify names via `lean_local_search` at start),
  `IsUnit.mul_iff`.
- **Sources**: [Loe] Prop 3.3.4 with proof; Silverman III.1 Table 1.2 (variable-change
  coefficient formulas).
- **Generality**: arbitrary `CommRing R` (Loeffler's proof is coefficient algebra +
  one sheaf-gluing step that is vacuous over a ring); no field/locality hypotheses.

### [T-E2] Universal Tate curve represents (ring level) — PROVABLE NOW · MILESTONE
- **Status**: open · **File**: Moduli/Representability.lean · `tateRing_homEquiv`
- **Depends on**: none (statement); the *display* with T-E1 · **Parallel**: yes ·
  **Type**: theorem
- **Statement**: in skeleton (`(tateRing →+* A) ≃ {c : A × A // IsUnit Δ(c)}`).
- **Proof sketch**: `MvPolynomial.eval₂Hom`-universal property gives
  `(MvPolynomial (Fin 2) ℤ →+* A) ≃ A²`; `IsLocalization.Away.lift` adds the
  `IsUnit (image Δ)` condition; assemble the equiv; naturality is definitional.
- **Mathlib needed**: `MvPolynomial.eval₂Hom`, `IsLocalization.Away.lift`,
  `IsLocalization.Away.AwayMap.lift_comp` (verify exact names).
- **Sources**: [Loe] Cor 3.3.5.
- **Generality**: all `CommRing A`, universe-polymorphic target.

### [T-A2] Construct the projective Weierstrass model (DS1)
- **Status**: open · **File**: EllipticCurve/WeierstrassModel.lean · `projModel`,
  `projModelπ`, `projModelZero`, `projModel_isWeierstrassModel`
- **Depends on**: none · **Parallel**: yes · **Type**: def + theorem
- **Statement/spec**: replace the DS1 sorries; prove `IsWeierstrassModel` for the
  construction.
- **Proof sketch**: two affine charts `Spec R[x,y]/(W_aff)` and `Spec R[t,s]/(W_∞)`
  (`t = −x/y`, `s = −1/y`), glued along `y`-inverted/`s`-inverted localisations via
  `Scheme.GlueData`; the section at infinity lands in chart 2 at `(t,s) = (0,0)`;
  point-bijection over fields: affine chart points ∪ {∞} ⟷ mathlib `Affine.Point`
  (`Point.zero ↔ ∞`, `Point.some ↔` chart-1 solutions).
- **Mathlib needed**: `Scheme.GlueData` (or two-open `Scheme.OpenCover` glue),
  `AlgebraicGeometry.Spec`, `IsLocalization.Away`.
- **Sources**: [KM] 2.2 (⧗KM for the quote); [Loe] Def 3.3.3; [Sil] III.3.
- **Generality**: any `CommRing R`; no ellipticity needed for the model itself.

### [T-A3] Model smooth ⟺ Δ unit
- **Status**: open (statement final; proof after T-A2) · **File**: WeierstrassModel.lean
  · `projModel_smooth` · **Depends on**: T-A2 · **Parallel**: with T-A4 · **Type**: thm
- **Sketch**: Jacobian criterion chartwise; mathlib `IsStandardSmooth` presentation of
  the chart rings; Δ-unit ⟺ fibrewise nonsingular (mathlib `IsElliptic` ↔ `Δ` unit ✓).
- **Sources**: [Loe] 3.3.3; [Sil] III.1.4(a). **Generality**: `CommRing R`.

### [T-A4] ⧗KM Uniqueness of the model (BB-RR consumer)
- **Status**: open · **File**: WeierstrassModel.lean · `isWeierstrassModel_unique`
- **Depends on**: T-A2 · **Parallel**: with T-A3 · **Type**: theorem
- **Sketch**: KM 2.2.5-route: both models are pointed smooth proper genus-1; RR
  black-box gives Weierstrass coordinates; two Weierstrass presentations differ by a
  `VariableChange`; transport. Quote-gate: KM 2.2.5 (full text needed); interim source
  Hida GME §2.2 (mine quote when cut).
- **Sources**: [KM] 2.2.5 ⧗ · [Hida-GME]. **Generality**: `CommRing R`.

### [T-A5] Base change of elliptic curves (Prop fields)
- **Status**: open · **File**: EllipticCurve/Basic.lean · `EllipticCurve.baseChange`
  (three Prop sorries) · **Depends on**: none · **Parallel**: yes · **Type**: lemma
- **Sketch**: `SmoothOfRelativeDimension`/`IsProper` base-change instances (mathlib,
  verify instance names); fibre condition: fibre of pullback ≅ fibre of original over
  the image point base-changed to the bigger residue field — use
  `Scheme.Hom.fiber`-pullback lemma (`Fiber.lean`'s `IsPullback` API) + transport of
  `IsWeierstrassModel` along residue-field extension (small lemma: `W.baseChange`
  compat of the points-interface).
- **Sources**: [Loe] §3.7 (Ell is fibered); [KM] 2.1 ⧗ (reconciliation only).
- **Generality**: arbitrary `g : T ⟶ S`.

### [T-A6a–d] ⧗KM Abel: the group law (DS2 discharge chain)
- **Status**: open (statements final) · **File**: EllipticCurve/GroupLaw.lean ·
  `grpObj` + `grpObj_one_eq_zero` + `grpObj_unique` + `grpObj_comm` +
  `pointAddCommGroup` + `point_smul_eq_comp_mulBy`
- **Depends on**: T-A2 (models), AG-LB *or* D-lane divisors (route choice = review Q3)
- **Parallel**: no (single chain; sub-tickets may split after route fixed)
- **Type**: def(data) + theorems
- **Sketch** (KM 2.1.2 route): (i) `I(P)` ideal sheaves of sections; (ii) rigidified
  `Pic⁰(E_T/T)` presheaf; (iii) Abel bijection `E(T) ≅ Pic⁰` (BB-COHBC stated black
  boxes: cohomology-and-base-change for `π_*O`, `R¹π_*O` line bundle); (iv) transport
  group structure; unit = zero section; (v) uniqueness/commutativity from Pic. This is
  the project's hardest chain — expect sub-ticketing via `/beastmode` Parent tickets.
- **Sources**: [KM] 2.1 ⧗ · Mumford AV p. 53 (per [Loe] 3.3.2's citation) ·
  [Hida-GME] §2.1. **Generality**: any base scheme.

### [T-B2] μ_N and (ℤ/N) wiring (DS3 discharge)
- **Status**: open · **File**: GroupScheme/MuN.lean · `muNGrpObj`, `constZModGrpObj`,
  `muNPointsEquiv` (+ its naturality, to be added as `muNPointsEquiv_natural`)
- **Depends on**: none · **Parallel**: yes · **Type**: def(data) + theorems
- **Sketch**: comult `Spec.map (T ↦ T ⊗ T)` on `ℤ[T]/(Tᴺ−1)`; pullback to `S`; GrpObj
  fields via `Over`-cartesian-monoidal API (pattern: mathlib
  `AlgebraicGeometry/Group/*.lean`); points: `Γ–Spec` adjunction + pullback universal
  property. `(ℤ/N)_S`: coproduct-indexed addition.
- **Mathlib needed**: `Over.cartesianMonoidalCategory` (local instance!), `ΓSpec`
  adjunction, `Sigma.desc`. **Sources**: [Loe] §3.2 example; [KM] 1.12 ⧗.
- **Generality**: any `S`, any `N ≥ 1` (étale statements separately, T-B7).

### [T-B3] E[N] ↪ E closed immersion + `torsionIdeal`
- **Status**: open · **Files**: Torsion.lean (`torsionι_isClosedImmersion`),
  LevelStructure/Basic.lean (`torsionIdeal` un-sorried via it)
- **Depends on**: T-A6 (uses only `mulBy` existence — statement-level OK now; proof
  uses separatedness of `π`) · **Parallel**: with T-B4/B5 · **Type**: theorem + def
- **Sketch**: zero section is a closed immersion (`π` separated; mathlib
  `isClosedImmersion_of_comp_eq_id` pattern seen in `Group/Abelian.lean`); closed
  immersions stable under pullback; convert via `IsClosedImmersion` ↔ ideal-sheaf
  (mathlib `IdealSheafData` dictionary).
- **Sources**: [KM] 1.3/2.3 ⧗; standard. **Generality**: any `N ≠ 0`.

### [T-B4] ⧗KM E[N]/S finite locally free of rank N² (KM 2.3.1; BB-FLAT)
- **Status**: open · **File**: Torsion.lean · `torsionπ_isFinite`, `torsionπ_flat`,
  `torsion_rank` · **Depends on**: T-B3; fibrewise degree input (HasseWeil/mathlib
  fibre theory) · **Parallel**: with T-B5 · **Type**: theorems
- **Sketch**: `[N]` proper + quasi-finite ⟹ finite (mathlib ZMT
  `IsFinite.of_isProper_of_locallyQuasiFinite` — verified present); fibrewise flatness
  criterion (BB-FLAT, stated black box) + fibre degree `N²` (Silverman III.6.2(d);
  fibre anchor: HasseWeil `mulByInt_degree`).
- **Sources**: [KM] 2.3.1 ⧗ · EGA IV 11.3.10 · [Sil] III.6.2.

### [T-B5] [N] étale when N invertible (+ E[N] finite étale)
- **Status**: open · **File**: Torsion.lean · `mulBy_etale`, `torsionπ_etale`
- **Depends on**: T-A6 (invariant differential input) · **Parallel**: with T-B4 ·
  **Type**: theorems
- **Sketch**: [Loe] 3.4.2(2) verbatim route: `[N]` multiplies the invariant
  differential by `N` ⟹ iso on (co)tangent ⟹ formally étale; + lfp. Needs the
  invariant-differential API (sub-ticket if mathlib's `Ω¹` for schemes is insufficient
  — check `RingTheory.Kaehler` sheafification status first).
- **Sources**: [Loe] Lemma 3.4.2(2) (quote in decomposition).

### [T-B6] Fibre comparison: E[N] geometric fibres ≅ (ℤ/N)² (reuse HasseWeil)
- **Status**: open · **New file**: EllipticCurve/TorsionFibre.lean · **Depends on**:
  T-B3 · **Parallel**: yes · **Type**: theorem
- **Sketch**: identify `E[N](k̄)` (scheme fibre points) with Weierstrass-model points
  via `IsWeierstrassModel.points`; then **import
  `HasseWeil.NTorsion.TorsionGeneralN`** (`E[N] ≃ₗ[ZMod N] (Fin 2 → ZMod N)`,
  alg. closed, `N` invertible) — do NOT re-prove. Cross-project import isolated here.
- **Sources**: [Sil] III.6.4(b); in-repo HasseWeil (sorry-free — verified).

### [T-C1] ⧗KM Weil pairing construction (DS4 discharge, KM 2.8)
- **Status**: open (BLOCKED on full KM text for the construction of record)
- **File**: WeilPairing/Basic.lean · `weilPairing`, `weilPairing_over` ·
  **Depends on**: T-B3, T-B2, T-D3 (divisor language) · **Type**: def(data) + theorem
- **Sketch**: KM 2.8 norm/divisor construction (⧗); candidate alternates to be
  reconciled at cut time: Oda/Deligne commutator on theta groups; Cartier autoduality.
  **Route choice is review question Q5.**
- **Sources**: [KM] 2.8 ⧗ · [Hida-GME] · [Sil] III.8 (fibre anchor).

### [T-C2] Pairing bilinear + alternating (specs)
- **Status**: open · **File**: WeilPairing/Basic.lean · `weilPairingEval_add_left`,
  `weilPairingEval_self` · **Depends on**: T-C1, T-A6d · **Parallel**: yes ·
  **Type**: theorems · **Sources**: [KM] 2.8 ⧗ / [Sil] III.8.1(a,b).

### [T-C3] Fibrewise nondegeneracy (spec)
- **Status**: open · **File**: WeilPairing/Basic.lean ·
  `weilPairingEval_nondegenerate` · **Depends on**: T-C1, T-C4 · **Type**: theorem ·
  **Sources**: [Sil] III.8.1(c) via T-C4 comparison.

### [T-C4] Comparison with HasseWeil field-level pairing + normalisation pin
- **Status**: open · **New file**: WeilPairing/FibreComparison.lean · **Depends on**:
  T-C1, T-B6 · **Parallel**: yes · **Type**: theorem
- **Sketch**: on geometric fibres, `weilPairingEval` agrees with
  `HasseWeil.weilPairing` (import; alg-closed ℓ-case first, composite N via CRT
  statement). This is what PINS the DS4 normalisation — the two conventions differ by
  inverse; decide per review Q6 and record.
- **Sources**: [Sil] III.8; in-repo HasseWeil `WeilPairing/{Pairing,PairingProps}`.

### [T-D1] ⧗(AG-LB) Official Cartier-divisor definition equivalence
- **Status**: blocked (AG-LB) · **File**: CartierDivisor.lean (statement to add when
  AG-LB lands) · **Type**: def + theorem · **Sources**: [KM] 1.1.1/1.2.3 (preview in
  hand — pull quotes when cutting).

### [T-D2] Full sets of sections: reduced-base criterion (KM 1.9.2)
- **Status**: open · **File**: CartierDivisor.lean ·
  `isFullSetOfSectionsAlg_iff_fields` · **Depends on**: none · **Parallel**: yes ·
  **Type**: theorem
- **Sketch**: KM 1.9.2's proof (in hand, quoted in decomposition): reduce to reduced
  `R`; equality of two elements of a reduced ring checked at geometric points of
  `Spec R[T₁..T_N]`; norm commutes with base change (`Algebra.norm` base-change lemma —
  verify name; else prove via `LinearMap.det` and `Matrix` base change).
- **Sources**: [KM] 1.9.1–1.9.2 with proofs (IN HAND).

### [T-D3] Divisor sums Σ[Pᵢ] (DS4a discharge)
- **Status**: open · **File**: CartierDivisor.lean · `sectionsDivisor`,
  `sectionsDivisor_degree` · **Depends on**: none · **Parallel**: yes ·
  **Type**: def(data) + theorem
- **Sketch**: section ⟹ closed immersion (π separated) ⟹ ideal sheaf via
  `Scheme.Hom.image`/IdealSheafData; product of finitely many ideal sheaves
  (add `IdealSheafData.mul` — small mathlib-shaped API, upstream candidate); finite
  locally free of degree n: locally, quotient by product of n "linear" ideals in a
  smooth relative curve — degree additivity via CRT off the diagonal + filtration on
  the diagonal (KM 1.1–1.2, preview in hand for quotes).
- **Sources**: [KM] 1.2.2 + 1.1 (in hand). **Generality**: smooth separated rel. curve.

### [T-D5] Exact order N ⟹ NP = 0 (KM 1.4.2; BB-DELIGNE)
- **Status**: open · **File**: ExactOrder.lean · `HasExactOrder.smul_eq_zero` ·
  **Depends on**: T-D3 · **Type**: theorem · **Sources**: [KM] 1.4.2 (IN HAND,
  verbatim in decomposition); black box BB-DELIGNE stated as its own lemma first.

### [T-D6] KM 1.4.4 (1)⇔(3): Drinfeld = naive when N invertible
- **Status**: open · **File**: ExactOrder.lean · `hasExactOrder_iff_geometric` ·
  **Depends on**: T-D3, T-B4 · **Parallel**: with T-D7 · **Type**: theorem
- **Sketch**: KM's proof IN HAND (preview pp. 18–19): (1)⟹(2) base change; (2)⟹(3)
  rank-N étale subgroup over field has N distinct points; (3)⟹(1) via (4). Attack
  obligation from decomposition D5 (killed-by-N hypothesis placement) must be resolved
  first — if the skeleton form is inequivalent, B2-report (do NOT silently edit).
- **Sources**: [KM] 1.4.4 with proof (IN HAND).

### [T-D7] KM 1.4.4 (1)⇔(4): étale-divisor criterion
- **Status**: open · **File**: ExactOrder.lean · `hasExactOrder_iff_etale` ·
  **Depends on**: T-D3 · **Parallel**: with T-D6 · **Type**: theorem ·
  **Sources**: [KM] 1.4.4 (IN HAND; discriminant argument quoted in proof).

### [T-D8] ⧗KM Γ(N): Drinfeld ⟺ naive (N invertible)
- **Status**: open · **File**: LevelStructure/Basic.lean · `isFullLevel_iff_naive` ·
  **Depends on**: T-D6, T-B4, T-B6 · **Type**: theorem ·
  **Sources**: [KM] 3.1 + 3.7 ⧗; [Loe] Fact 3.8.1 (naive side, in hand).

### [T-D9] Γ₁(N): Drinfeld ⟺ naive (restatement of T-D6)
- **Status**: open · **File**: LevelStructure/Basic.lean · `isGammaOne_iff_naive` ·
  **Depends on**: T-D6 · **Type**: theorem (thin wrapper — golf target).

### [T-D10] ⧗KM Γ₀(N): literal fppf-local cyclicity
- **Status**: open (statement to add) · **File**: LevelStructure/Basic.lean ·
  **Depends on**: T-D3; fppf vocabulary · **Type**: def + equivalence statement ·
  **Sources**: [KM] 1.4.1 cyclic (IN HAND) + 3.4 ⧗ + 6.1 ⧗.

### [T-E3] Ell/R category plumbing (Prop sorries)
- **Status**: open · **File**: Moduli/EllCategory.lean · category instance fields,
  `pullbackAlongMap.isPullback/zero_w` · **Depends on**: none · **Parallel**: yes ·
  **Type**: lemmas · **Sketch**: `IsPullback.of_id_fst`-style + `IsPullback.paste_horiz`
  (find exact names); EllHom ext-lemma discipline.

### [T-E4] Moduli-problem functor laws (Prop sorries)
- **Status**: open · **File**: Moduli/Representability.lean · `gammaOneNaiveProblem`
  and `gammaFullNaiveProblem` `map_id/map_comp/map`-membership sorries ·
  **Depends on**: T-E3 · **Type**: lemmas.

### [T-E5] ⧗KM + AG-QUOT: representable ⟺ rel. representable + rigid (KM 4.7)
- **Status**: open · **File**: Moduli/EllCategory.lean · `representable_iff` ·
  **Depends on**: AG-QUOT (Loeffler 3.6.1, quote in hand), naive-Γ(3)/Legendre
  bootstrap objects (sub-tickets at cut time), T-E4 · **Type**: theorem (hard) ·
  **Sources**: [Loe] 3.7.4 + proof sketch (in hand); [KM] 4.7 ⧗.

### [T-E7] Y₁(N) representable + smooth affine (N ≥ 4, N invertible) · MILESTONE
- **Status**: open · **File**: Moduli/Representability.lean ·
  `gammaOneNaive_representable` · **Depends on**: T-E1, T-E2, T-D6, T-B5, T-E4 ·
  **Type**: theorem ·
  **Sketch**: Loeffler §3.3.6 explicit construction (universal Tate curve; cut out
  order-exactly-N locus via division polynomials; remove lower-order loci; invert N)
  + Thm 3.4.4 smoothness (formal criterion via `[N]` étale — proof sketch in hand).
- **Sources**: [Loe] Def 3.3.6 + Thm 3.4.4 (verbatim in decomposition).

### [T-E8] Stack packaging (pseudofunctor + IsStack statement)
- **Status**: open · **File**: Moduli/Stack.lean (extend) · **Depends on**: T-E3 ·
  **Type**: def + statement · **Sketch**: `S ↦ groupoid of (E/S)` pseudofunctor;
  state `Pseudofunctor.IsStack fppfTopology`; proof = T-E10 + separatedness (sorried
  until BB-DESC route chosen). *Bridge artifact — not load-bearing (plan D3).*

### [T-E9] ⧗KM Y(N) rigid + representable (N ≥ 3) · MILESTONE
- **Status**: open · **File**: Moduli/Representability.lean ·
  `gammaFullNaive_representable` · **Depends on**: T-E5 *or* explicit route via
  T-E7-style construction; T-C1 (Weil-pairing open locus per Loeffler 3.8.2); T-D8 ·
  **Type**: theorem · **Sources**: [Loe] 3.8.2/3.8.3 (in hand); [KM] 5.1 ⧗.

### [T-E10] fppf descent for elliptic curves (BB-DESC consumer)
- **Status**: open · **File**: Moduli/Stack.lean · `ellipticCurve_fppf_descent` ·
  **Depends on**: T-A5 · **Type**: theorem · **Sources**: SGA 1 VIII (black box
  statement first as its own lemma); [KM] 4.1 ⧗ context.

### [T-E11] fppf separatedness of relatively representable problems
- **Status**: open · **File**: Moduli/Stack.lean · `moduliProblem_fppf_separated` ·
  **Depends on**: T-E3 · **Type**: theorem (direct from rel. representability +
  fppf-surjectivity ⟹ epi on points — check mathlib `Surjective` API).

### [T-F0] Roots-of-unity count in ℚ̄
- **Status**: open · **File**: ModularCurve/YRho.lean · `card_rootsOfUnity_algClosureQ`
  · **Depends on**: none · **Parallel**: yes · **Type**: lemma ·
  **Sketch**: `Xᴺ − 1` separable in char 0 + alg. closed ⟹ N distinct roots; mathlib
  `IsPrimitiveRoot`/`Polynomial.nthRoots` card lemmas (search first — likely nearly
  present).

### [T-F1] ⧗(AG-GG) V_ρ construction (DS5 discharge)
- **Status**: open (scoping first: AG-GG sub-development) · **File**: YRho.lean ·
  `vRho`, `vRhoπ`, `vRhoPointsEquiv` + specs T-F1a/b (+ group structure T-F1c) ·
  **Type**: def(data) + theorems ·
  **Sketch**: splitting field `L` of ρ (finite Galois); descent datum on the constant
  scheme `(ℤ/N)²_L` twisted by ρ; affine Galois descent = `Spec` of invariants
  (AG-QUOT-adjacent); étale-ness from `L/ℚ` étale. Loeffler §3.6's "scary lemma
  (étale descent of morphisms)" quote anchors the mechanism.

### [T-F3] ρ-level structure: scheme-level compat (discharges DS5d)
- **Status**: open · **File**: YRho.lean · unfold `PairingCompatAt` via `Γ–Spec` iso;
  upgrade `coords_additive`/`pairing_compat` to morphism-level once T-F1c lands ·
  **Depends on**: T-F1, T-C4 · **Type**: def + theorems.

### [T-F4] ⧗ Y(ρ̄_N) representable (phase-3 headline) · MILESTONE
- **Status**: open (phase 3) · **File**: YRho.lean · `yRho_representable` ·
  **Depends on**: T-E9, T-F1, T-F3, AG-QUOT (twisting) · **Type**: theorem ·
  **Sources**: [Buz-L8] p. 33 (verbatim in decomposition); twist route in plan.

### [T-F5] Geometric irreducibility (BB-IRR)
- **Status**: open (phase 3; black box acceptable indefinitely per owner) ·
  **File**: YRho.lean · `yRho_geometricallyIrreducible` · **Depends on**: T-F4 ·
  **Sources**: [Buz-L8] pp. 33–34 ("Proof: See 1980s.").

---

## Cleanup cadence (algorithmic; every cleanup ALSO enforces: no `set_option
maxHeartbeats` anywhere; DS-register unchanged; `#print axioms` audit)

- **[CLEANUP-1]** after T-A2+T-A3+T-A4 → `/cleanup` WeierstrassModel.lean (deps: those)
- **[CLEANUP-2]** after T-A5 (final per-file, Basic.lean; +T-A6d touches GroupLaw —
  final GroupLaw cleanup folds in after T-A6 chain) (deps: T-A5, T-A6)
- **[CLEANUP-3]** after T-B3+T-B4+T-B5 → Torsion.lean (deps: those)
- **[CLEANUP-4]** final per-file MuN.lean (deps: T-B2) — includes `ULift` review in
  `muNRing`
- **[CLEANUP-5]** after T-D2+T-D3 → CartierDivisor.lean (deps: those) — includes
  upstreaming review of `IdealSheafData.mul`
- **[CLEANUP-6]** after T-D5+T-D6+T-D7 → ExactOrder.lean (deps: those)
- **[CLEANUP-7]** final per-file LevelStructure/Basic.lean (deps: T-D8, T-D9)
- **[CLEANUP-8]** after T-E3+T-E4 → EllCategory.lean (deps: those)
- **[CLEANUP-ALL-1]** before milestone T-E7: `/cleanup-all` on the project so far
  (deps: all open A/B/D/E tickets above it)
- **[CLEANUP-ALL-2]** before milestone T-E9 (deps: T-C1..T-C4, T-D8)
- **[CLEANUP-FINAL]** `/cleanup-all` — last ticket of the phase (deps: everything);
  hands to `/pre-submit`.

## Board totals check
24 work + 11 cleanup = 35; ⌈24/3⌉ = 8 ≤ 8 per-file/interval cleanups + 2 pre-milestone
+ 1 final ✓ cadence satisfied.
