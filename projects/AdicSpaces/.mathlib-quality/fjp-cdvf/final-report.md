# FJP → CDVF campaign — K12 final report (acceptance sweep)

**Verdict: ALL ACCEPTANCE GATES PASS.**

Worktree `/Users/mcu22seu/Documents/GitHub/aintlib-adic-fjp`, branch `fjp/cdvf-lemma51`,
base HEAD `79f069da0` (dev/adic-spaces), campaign HEAD `ae4a1ef57`. Sweep run 2026-07-22 by the
K12 verification worker. This document is READ-ONLY reporting — no `.lean` file was modified.

The campaign generalises the Laurent-only finite-jet pinching development ([FJP] Theorem 1.3) to an
arbitrary complete discretely valued nonarchimedean field (CDVF) base, formalising [FJP] Lemma 5.1
(Koszul exactness / strictness / closed images / eqs (9)–(10)) over the restricted Tate algebra and
re-deriving all Theorem-1.1/1.3 endpoints generically, with the five original Laurent headliners
recovered verbatim as specialisations and an independent p-adic (`ℚ_[p]`) regression witness.

| # | Gate | Result |
|---|------|--------|
| 1 | Axiom audit (70 headline decls) | **PASS** — every decl `{propext, Classical.choice, Quot.sound}`; 0 `sorryAx` |
| 2 | Added-line scan (`sorry`/`admit`/`axiom`/`unsafe`) | **PASS** — 0 banned tokens; 11 benign `set_option` (itemised) |
| 3 | FJP tree sorry-free | **PASS** — grep empty |
| 4 | Frozen five byte-check | **PASS** — `FiniteJetMain.lean` byte-identical to base; 5 statements verbatim |
| 5 | Targeted + umbrella builds | **PASS** — 24/24 `EXIT:0`; umbrella 3307 jobs |
| 6 | `git diff --check` | **PASS** — clean (working tree + full range) |
| 7 | Paper→Lean crosswalk | **PASS** — every paper object/clause mapped to a delivered decl |
| 8 | Proof-method divergences | **PASS** — exactly 3, each a same-theorem route change (documented) |
| 9 | New declaration inventory | **PASS** — headline decls + types listed per module |
| 10 | Commit range + stats | 15 commits; 25 files, +11663 / −687 |

---

## 1. Axiom audit (PASS)

Method: scratch file `scratchpad/axiom_probe.lean` importing all headline-bearing modules, `#print
axioms` on every headline, run with `lake env lean` (exit 0). Grep of the combined output:
`sorryAx` occurrences = **0**; `error`/`unknown identifier`/`does not depend`/`declaration uses` =
**0**; stray axiom tokens (`Classical.em`, `*.ax*`) = **0**. All **70** declarations resolve and
depend on **exactly `{propext, Classical.choice, Quot.sound}`**.

Every row below = `[propext, Classical.choice, Quot.sound]` ⇒ **PASS**.

**CDVFBase (K1)** — `FiniteJetOver.Uniformizer.ofDVR`, `FiniteJetOver.unitBall_eq_integer`,
`FiniteJetOver.isNoetherianRing_unitBall`.
**AdicCompletionPrincipal (K2a)** — `AdicCompletion.isNoetherianRing_span_singleton`.
**KoszulFiniteFree (K3)** — `FiniteJet.KoszulFree.koszulDifferential_comp`.
**GraphKoszul d1/d2 (K3)** — `FiniteJet.GraphKoszul.koszulDifferential_zero_eq_d1`,
`FiniteJet.GraphKoszul.koszulDifferential_one_eq_d2`.
**CDVFNoetherian (K2c)** — DVR layer: `FiniteJetOver.isNoetherianRing_unitBall_P`,
`FiniteJetOver.isNoetherianRing_P`, `FiniteJetOver.isStronglyNoetherian`; Uniformizer layer:
`FiniteJetOver.Uniformizer.isNoetherianRing_unitBall_P`,
`FiniteJetOver.Uniformizer.isNoetherianRing_P`, `FiniteJetOver.Uniformizer.isStronglyNoetherian`.
**KoszulFreeExactness (K4)** — `FiniteJet.KoszulFree.koszulDifferential_coordinate_exact`,
`FiniteJet.KoszulFree.koszulGraph_polynomial_exact`.
**GraphKoszul restricted / strict / (9) / (10) (K5–K7)** —
`FiniteJet.GraphKoszul.koszulGraph_restricted_exact`,
`FiniteJet.GraphKoszul.koszulGraph_exact_strict_closed`,
`FiniteJet.GraphKoszul.exists_d1_lift_pow`,
`FiniteJet.GraphKoszul.pow_smul_graphIdeal_inter_unitBall_subset`,
`FiniteJet.GraphKoszul.exists_d2_lift_pow`,
`FiniteJet.GraphKoszul.pow_smul_ker_d1_inter_subset`.
**FiniteJetOver JetA endpoints (K8d)** — `FiniteJetOver.isSheafy_JetA`,
`FiniteJetOver.isSheafy_JetA_of_dvr`, `FiniteJetOver.isUniform_JetA`,
`FiniteJetOver.not_isNoetherianRing_JetA`, `FiniteJetOver.not_isStablyUniform_JetA`.
**FiniteJetOver `finiteJet_*` endpoints, layer 1 / explicit ϖ (K9)** — `finiteJet_isUniform`,
`finiteJet_isDomain`, `finiteJet_not_noetherian`, `finiteJet_not_stablyUniform`,
`finiteJet_isSheafyFor`, `finiteJet_isSheafOfTopologicalRings`,
`finiteJet_structurePresheaf_isSheafOfTopologicalRings`, `finiteJet_structurePresheaf_isSheaf`,
`finiteJet_isSheafyFor_all`, `finiteJet_isSheafyTateRing`,
`finiteJet_structurePresheaf_isSheafOfTopologicalRings_all`,
`finiteJet_structurePresheaf_isSheaf_all`,
`finiteJet_completionModel_structurePresheaf_isSheafOfTopologicalRings`,
`finiteJet_completionModel_structurePresheaf_isSheaf` (all in `FiniteJetOver`).
**FiniteJetOver `finiteJet_*` endpoints, layer 2 / `_of_dvr` (K9)** — the twelve `_of_dvr`
counterparts: `finiteJet_isUniform_of_dvr`, `finiteJet_not_stablyUniform_of_dvr`,
`finiteJet_isSheafyFor_of_dvr`, `finiteJet_isSheafOfTopologicalRings_of_dvr`,
`finiteJet_structurePresheaf_isSheafOfTopologicalRings_of_dvr`,
`finiteJet_structurePresheaf_isSheaf_of_dvr`, `finiteJet_isSheafyFor_all_of_dvr`,
`finiteJet_isSheafyTateRing_of_dvr`,
`finiteJet_structurePresheaf_isSheafOfTopologicalRings_all_of_dvr`,
`finiteJet_structurePresheaf_isSheaf_all_of_dvr`,
`finiteJet_completionModel_structurePresheaf_isSheafOfTopologicalRings_of_dvr`,
`finiteJet_completionModel_structurePresheaf_isSheaf_of_dvr`.
**Padic regression (K11)** — `FiniteJetOver.Padic.instIsDiscreteValuationRing`,
`padicFiniteJet_isUniform`, `padicFiniteJet_isDomain`, `padicFiniteJet_not_noetherian`,
`padicFiniteJet_not_stablyUniform`, `padicFiniteJet_isSheafyTateRing`,
`padicFiniteJet_isSheafyFor_all`, `padicFiniteJet_isSheafyComplete`,
`padicFiniteJet_structurePresheaf_isSheafOfTopologicalRings_all`,
`padicFiniteJet_structurePresheaf_isSheaf_all`,
`padicFiniteJet_completionModel_structurePresheaf_isSheafOfTopologicalRings`,
`padicFiniteJet_completionModel_structurePresheaf_isSheaf` (all in `FiniteJetOver.Padic`).
**LaurentCompat / recovered wrappers (K10)** — `FiniteJet.Compat.jetA_eq`,
`FiniteJet.Compat.finiteJet_isSheafy`, `FiniteJet.Compat.finiteJet_isUniform`,
`FiniteJet.Compat.finiteJet_isDomain`, `FiniteJet.Compat.finiteJet_not_noetherian`,
`FiniteJet.Compat.finiteJet_not_stablyUniform`.

**Note on the pre-existing project sorries.** The umbrella build emits `declaration uses sorry`
warnings for `AdicCompletionNoetherian.lean:976,1440` and `ContinuousValuations.lean:255` — these
are non-FJP, producer-WIP files that the campaign deliberately avoided (crosswalk: "do NOT
import/use `AdicCompletionNoetherian.isNoetherianRing` — sorried"). The axiom probe proves no FJP
headline transitively depends on any of them (a `sorryAx` would otherwise appear). Independent of
the grep, `#print axioms` is the real gate — and it is clean for all 70.

## 2. Added-line scan (PASS)

`git diff 79f069da0..HEAD -- '*.lean'`, added lines (`^+`, excluding `+++`):

- **`sorry` / `admit` / `axiom` / `unsafe` keyword tokens: 0.** The word-boundary scan is empty; a
  broader substring scan hits only `admitting` / `admits` in two docstrings
  (`…closed chains admitting such a w…`, `…image admits a norm-bounded lift…`) — English prose, not
  the `admit` tactic. **No banned token in any added line. (This is the hard-fail gate — clean.)**
- **`set_option`: 11 added occurrences, all benign** (transparency flag or heartbeat limit — never a
  banned token). Attributed by file:

  *Prompt-itemised (8), reconfirmed necessary by the K8d worker:*
  - `Over/StrictLocalization.lean:94,124,1091,1182,1192` — `backward.isDefEq.respectTransparency false in` (5)
  - `Over/Functoriality.lean:47` — `backward.isDefEq.respectTransparency false` (file-wide)
  - `Over/Functoriality.lean:2201` — `backward.isDefEq.respectTransparency true in` (restore)
  - `Over/SheafTransfer.lean:373` — `maxHeartbeats 6400000 in` (on `gluing_JetA`)

  *Additional, crosswalk-documented (3) — also benign, no banned token:*
  - `Over/UniformDomain.lean:122,164` — `maxHeartbeats 1000000 in` (2); mirror the Laurent
    `FiniteJetUniformDomain.lean:209,252` heartbeat bumps that the generic port reproduces.
  - `FJP/RestrictedGaussAdic.lean:369` — `backward.isDefEq.respectTransparency false in`; the K2b
    AdicBridge extraction site (crosswalk D4/R5: "the set_option sites travel with their decls").

## 3. FJP tree sorry-free (PASS)

`grep -rn '\bsorry\b\|\badmit\b' 'projects/AdicSpaces/Adic spaces/FJP/'` → **empty** (exit 1). The
entire FJP directory (new + modified modules, `Over/` included) contains no `sorry`/`admit`.

## 4. Frozen five byte-check (PASS)

`git show 79f069da0:'…/FJP/FiniteJetMain.lean'` vs the working copy → `diff` exit **0**
(byte-identical; the five Theorem-1.3 headliners are untouched across the whole campaign). Verbatim
statement lines (`FiniteJetMain.lean`):

```
27: theorem finiteJet_isSheafy : ValuationSpectrum.IsSheafy (JetA F) :=
31: theorem finiteJet_isUniform : TopologicalRing.IsUniform (JetA F) :=
35: theorem finiteJet_isDomain : IsDomain (JetA F) :=
39: theorem finiteJet_not_noetherian : ¬ IsNoetherianRing (JetA F) :=
43: theorem finiteJet_not_stablyUniform : ¬ TopologicalRing.IsStablyUniform (JetA F) :=
```

## 5. Targeted + umbrella builds (PASS)

Each `lake build '<target>'; echo EXIT:$?` (Bash only, no pipe). All **EXIT:0**. Job counts are the
full dependency-tree size lake reports per target (all incremental / cached after the umbrella).

| Target | Jobs | Exit |
|---|---|---|
| `«Adic spaces».FJP.CDVFBase` | 3125 | 0 |
| `«Adic spaces».FJP.AdicCompletionPrincipal` | 1839 | 0 |
| `«Adic spaces».FJP.KoszulFiniteFree` | 1363 | 0 |
| `«Adic spaces».FJP.RestrictedGaussAdic` | 3121 | 0 |
| `«Adic spaces».FJP.CDVFNoetherian` | 3128 | 0 |
| `«Adic spaces».FJP.KoszulFreeExactness` | 1736 | 0 |
| `«Adic spaces».FJP.KoszulRestrictedExactness` | 3133 | 0 |
| `«Adic spaces».FJP.KoszulStrictClosed` | 3135 | 0 |
| `«Adic spaces».FJP.Over.JetRings` | 3126 | 0 |
| `«Adic spaces».FJP.Over.UniformDomain` | 3129 | 0 |
| `«Adic spaces».FJP.Over.Chart` | 3137 | 0 |
| `«Adic spaces».FJP.Over.StrictLocalization` | 3133 | 0 |
| `«Adic spaces».FJP.Over.Functoriality` | 3141 | 0 |
| `«Adic spaces».FJP.Over.SheafTransfer` | 3142 | 0 |
| `«Adic spaces».FJP.Over.SheafyEndpoints` | 3159 | 0 |
| `«Adic spaces».FJP.Over.ExamplePadic` | 3165 | 0 |
| `«Adic spaces».FJP.Over.LaurentCompat` | 3160 | 0 |
| `«Adic spaces».FJP.FiniteJetGraphKoszul` **(mandated)** | 3123 | 0 |
| `«Adic spaces».FJP.FiniteJetStrictLocalization` **(mandated)** | 3125 | 0 |
| `«Adic spaces».FJP.FiniteJetSheafyEndpoints` **(mandated)** | 3148 | 0 |
| `«Adic spaces».FJP.FiniteJetNoetherianVertices` (modified) | 3122 | 0 |
| `«Adic spaces».FJP.RestrictedLaurent` (modified) | 3116 | 0 |
| `«Adic spaces».FJP.FiniteJetUniformDomain` (modified) | 3122 | 0 |
| `«Adic spaces»` **(umbrella, mandated)** | **3307** | **0** |

Umbrella: `Build completed successfully (3307 jobs).` — no `error:` lines anywhere in the sweep.

## 6. `git diff --check` (PASS)

`git diff --check` → exit **0** (working tree clean); `git diff --check 79f069da0..HEAD` → exit
**0** (no whitespace errors / conflict markers introduced across the campaign).

## 7. Paper → Lean crosswalk (PASS)

Every paper object and every Lemma-5.1 clause maps to a delivered, axiom-clean declaration
(namespaces verbatim; `exists` = already generic in the pre-campaign tree).

| Paper item | Delivered Lean declaration |
|---|---|
| base field `k`, ring `k°`, uniformizer `ϖ` | `[NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]`, `𝒪[K]`, `FiniteJetOver.Uniformizer K` + `.ofDVR` |
| rings `L₀,B₀,C₀,D₀,A₀` (§1) | generic `FiniteJetOver.{JetC,JetB,JetD,JetA}` (`Over/JetRings.lean`); Laurent `FiniteJet.*` recovered via `FiniteJet.Compat.jetA_eq` |
| Milnor row (4), maps ρ/κ | `FiniteJetOver.milnorRow_exact`; `piA/piB/piC/piD` uniformizer family |
| `P_E = E⟨T₁…T_m⟩`, `P_{E,0}` (§5.1) | `FiniteJet.GraphKoszul.P E m` (`RestrictedGaussAdic.lean`), `unitBall (P E m)` |
| `r_i = gT_i − f_i`, `d_{1,E}`, `J_E` (eq. 2) | subset-model `FiniteJet.KoszulFree.koszulDifferential`; `d1`/`Ideal.span (Set.range r)`; conjugations `koszulDifferential_zero_eq_d1`, `koszulDifferential_one_eq_d2` |
| **Lemma 5.1 (1)** Koszul exact in positive degrees | `FiniteJet.GraphKoszul.koszulGraph_restricted_exact : … (q) : Function.Exact (koszulDifferential r (q+1)) (koszulDifferential r q)` |
| **Lemma 5.1 (2)** every differential strict | `FiniteJet.GraphKoszul.koszulDifferential_isStrict` (+ `KoszulStrictClosed.isStrictLinearMap_of_lift` bridge) |
| **Lemma 5.1 (2)** every image closed | `FiniteJet.GraphKoszul.isClosed_range_koszulDifferential` |
| **Lemma 5.1 (3)** `J_E` closed | `FiniteJet.GraphKoszul.isClosed_graphIdeal` (exists); bundled in `koszulGraph_exact_strict_closed` (clauses 1–3) |
| **eq. (9)** `ϖ^{h_E}(J_E ∩ P_{E,0}) ⊆ d_{1,E}(P_{E,0}^m)` | `exists_d1_lift_pow` (∃-h norm form) + `pow_smul_graphIdeal_inter_unitBall_subset` (lattice form) |
| **eq. (10)** `ϖ^z(ker d_{1,D} ∩ P_{D,0}^m) ⊆ d_{2,D}(⋀² P_{D,0}^m)` | `exists_d2_lift_pow` (∃-z norm form) + `pow_smul_ker_d1_inter_subset` (lattice form; generic E, specialised D) |
| noetherian vertices (asserted §5.1) | `AdicCompletion.isNoetherianRing_span_singleton` → `FiniteJetOver.isNoetherianRing_unitBall_P` → `isNoetherianRing_P` → `isStronglyNoetherian` |
| **Thm 1.1 / 1.3 endpoints, general `K`** | `FiniteJetOver.{isSheafy_JetA, isUniform_JetA, finiteJet_isDomain, not_isNoetherianRing_JetA, not_isStablyUniform_JetA}` + real presheaf `finiteJet_structurePresheaf_isSheaf_all` / `…isSheafOfTopologicalRings_all` / `…completionModel…` (both layers) |
| Thm 1.1 endpoints, Laurent (FROZEN) | `FiniteJet.finiteJet_*` in `FiniteJetMain.lean` (byte-identical) — recovered as `FiniteJet.Compat.finiteJet_*` specialisations |
| p-adic regression witness | `FiniteJetOver.Padic.padicFiniteJet_*` at `K = ℚ_[p]` (`𝒪[ℚ_[p]]` DVR via `instIsDiscreteValuationRing`) |

## 8. Proof-method divergences (PASS — exactly three)

These are the **only** three departures from the printed proof; each proves the identical theorem by
a different but equivalent route, and every other step follows [FJP] §5.1 verbatim.

**(a) K4 Part A — multidegree-component route (not the printed mapping-cone induction on m).**
Paper Step 2 proves coordinate-sequence exactness by identifying a mapping-cone block under
`finSuccEquiv` and inducting on the number of variables. Lean's
`koszulDifferential_coordinate_exact` instead decomposes each Koszul term into its
`MvPolynomial` multidegree components (`koszulComponent` / `indexDegree` / `sum_koszulComponent`,
`koszulComponent_differential`) and proves exactness component-by-component. Same theorem
(coordinate sequence `(X_i)` is regular ⇒ Koszul exact in positive degrees over an arbitrary
`CommRing A`); the multidegree grading is a standard, cleaner presentation of the same regular-
sequence acyclicity.

**(b) K4 Part B — localise over the standard cover of `{C g} ∪ {r_i}` (not at maximal ideals).**
Paper Steps 1–2 argue "exactness is local at primes" and split at each prime `𝔭`: some `r_j ∉ 𝔭`
(insertion homotopy `h(ω)=r_j^{-1}e_j∧ω`, `dh+hd=id`) vs. all `r_i ∈ 𝔭` (write `1=a₀g+Σaᵢfᵢ`, so `g`
is a local unit, translate `T_i ↦ T_i+f_i/g`, reduce to the coordinate sequence). Lean's
`koszulGraph_polynomial_exact` runs **the same case split** but over the standard affine cover of the
spanning family `{C g} ∪ {r_i}` (unit-ideal hypothesis `Ideal.span ({g} ∪ Set.range f) = ⊤`):
`koszulDifferential_exact_of_isUnit` (insertion-homotopy branch, via
`koszulDifferential_insertion_cancel`) and `koszulGraph_exact_of_isUnit_base` + `mvTranslationEquiv`
(g-unit branch), glued by `exact_of_localized_maximal` on localised terms
(`isLocalizedModule_map_koszulDifferential`). This avoids building a localization tower while making
exactly the paper's two-case argument; the standard cover is the constructive form of "local at
primes".

**(c) K5 — all-degree exactness by flat base change (not a per-degree equational-criterion redo).**
Paper Step 3 pushes exactness from `E[T_•]` to `P_E` by `ϖ`-adic completion + inverting `ϖ`, flat by
Stacks 00MB. Lean's `koszulDifferential_baseChange_exact` transfers **all** degrees at once with
`Module.Flat.lTensor_exact` (using `flat_polyToP`) after identifying
`K_q(P_E) ≅ K_q(E[T_•]) ⊗ P_E` via `koszulTermBaseChange` — it does **not** repeat the degree-1
equational-criterion argument in every degree. Same flatness input, same conclusion, applied
uniformly.

No other divergences: signs/indexing follow extraction §4 (`(-1)^{#{j∈J | j<i}}`), (9)/(10) are the
bounded-denominator criterion (1) applied to `d_{1,E}` and `d_{2,D}`, and the endpoint chain
5.1→…→1.1 mirrors the paper.

## 9. New declaration inventory (headlines + types)

**`FJP/CDVFBase.lean`** (K1, namespace `FiniteJetOver`). `structure Uniformizer K` (fields `elem :
𝒪[K]`, `irreducible`); `noncomputable def Uniformizer.ofDVR [IsDiscreteValuationRing 𝒪[K]] :
Uniformizer K`; `theorem unitBall_eq_integer : FiniteJet.unitBall K = 𝒪[K]`; `noncomputable def
unitBallEquivInteger : FiniteJet.unitBall K ≃+* 𝒪[K]`; `theorem isNoetherianRing_unitBall
[IsDiscreteValuationRing 𝒪[K]] : IsNoetherianRing (FiniteJet.unitBall K)`. (Derived facts:
`isUnit_val`, `norm_val_pos/_lt_one`, `norm_val_pow_mul`, `tendsto_pow_val`, `isTateRing`.)

**`FJP/AdicCompletionPrincipal.lean`** (K2a, namespace `AdicCompletion`). `def ofPowerSeries : R⟦X⟧
→+* AdicCompletion (Ideal.span {a}) R`; `theorem ofPowerSeries_surjective : Function.Surjective
(ofPowerSeries a)`; `theorem isNoetherianRing_span_singleton (R) [CommRing R] [IsNoetherianRing R]
(a : R) : IsNoetherianRing (AdicCompletion (Ideal.span {a}) R)`; bonus `isNoetherianRing_of_isPrincipal`.

**`FJP/KoszulFiniteFree.lean`** (K3, namespace `FiniteJet.KoszulFree`). `abbrev KoszulIndex (m q) :=
{I : Finset (Fin m) // I.card = q}`; `abbrev KoszulTerm R m q := KoszulIndex m q → R`; `def
koszulDifferential (r : Fin m → R) (q) : KoszulTerm R m (q+1) →ₗ[R] KoszulTerm R m q` with
`koszulDifferential_apply`; `theorem koszulDifferential_comp (r) (q) : koszulDifferential r q ∘ₗ
koszulDifferential r (q+1) = 0` (d²=0, via the `pairTerm` involution); `koszulDifferential_continuous`.

**`FJP/KoszulFreeExactness.lean`** (K4, namespace `FiniteJet.KoszulFree`). `theorem
koszulDifferential_coordinate_exact (A) [CommRing A] (m q) : Function.Exact (koszulDifferential
(fun i => (X i : MvPolynomial (Fin m) A)) (q+1)) (koszulDifferential (X ·) q)`; `theorem
koszulGraph_polynomial_exact (g) (f : Fin m → A) (hunit : Ideal.span ({g} ∪ Set.range f) = ⊤) (q) :
Function.Exact (koszulDifferential (fun i => C g * X i − C (f i)) (q+1)) (… q)`.

**`FJP/RestrictedGaussAdic.lean`** (K2b, namespaces `FiniteJet`, `FiniteJet.GraphKoszul`). `abbrev P
(E) [NormedCommRing E] [IsUltrametricDist E] (m) : Type_` (the Gauss-normed restricted Tate algebra
`E⟨T₁…T_m⟩`); `noncomputable def polyToP : MvPolynomial (Fin m) E →+* P E m`; `noncomputable def
polyBall`; `noncomputable abbrev I0 : Ideal (MvPolynomial (Fin m) (unitBall E))` (the principal
`span {C ⟨ϖ,…⟩}`); `noncomputable def toAdic : unitBall (P E m) →+* AdicCompletion I0 …`;
`noncomputable def ballAdicEquiv : unitBall (P E m) ≃+* AdicCompletion …`; `theorem flat_polyToP
(hE₀ : IsNoetherianRing (unitBall E)) … : Module.Flat (MvPolynomial (Fin m) E) (P E m)`.

**`FJP/CDVFNoetherian.lean`** (K2c, namespace `FiniteJetOver` + `Uniformizer` sublayer). `theorem
isNoetherianRing_mvPolynomial_unitBall [IsDiscreteValuationRing 𝒪[K]] (m)`; DVR layer `theorem
isNoetherianRing_unitBall_P`, `isNoetherianRing_P`, `instance isStronglyNoetherian
[IsDiscreteValuationRing 𝒪[K]] : IsStronglyNoetherian K`; explicit-ϖ layer
`Uniformizer.isNoetherianRing_unitBall_P/_P/_isStronglyNoetherian`.

**`FJP/FiniteJetGraphKoszul.lean`** (K3 append, namespace `FiniteJet.GraphKoszul`). `theorem
koszulDifferential_zero_eq_d1 (r) (x : KoszulTerm S m 1) : koszulTermZeroEquiv (koszulDifferential r
0 x) = d1 r (koszulTermOneEquiv x)`; `theorem koszulDifferential_one_eq_d2 (r) (x : KoszulTerm S m 2)
(j) : koszulTermOneEquiv (koszulDifferential r 1 x) j = d2 r (koszulTermTwoEquiv x) j` (sign-checked
conjugations to the existing degree-1/2 layer).

**`FJP/KoszulRestrictedExactness.lean`** (K5, namespaces `FiniteJet.KoszulFree`,
`FiniteJet.GraphKoszul`). `theorem koszulDifferential_baseChange_exact [Module.Flat R B] {r} (q)
(hex) : Function.Exact (koszulDifferential (algebraMap R B ∘ r) (q+1)) (… q)`; `theorem
koszulGraph_restricted_exact (hE₀ : IsNoetherianRing (unitBall E)) (t)(htu)(ht1)(ht0)(hscale)
(g)(f)(hunit)(r)(hr : ∀ i, r i = polyToP (C g * X i − C (f i))) (q) : Function.Exact
(koszulDifferential r (q+1)) (koszulDifferential r q)` — **Lemma 5.1 clause 1**.

**`FJP/KoszulStrictClosed.lean`** (K6+K7, namespaces `FiniteJet`, `FiniteJet.GraphKoszul`). `theorem
isStrictLinearMap_of_lift` (no-Baire OMT bridge); `theorem isClosed_range_koszulDifferential
[IsNoetherianRing (P E m)] …`; `theorem koszulDifferential_isStrict …`; `theorem
koszulGraph_exact_strict_closed … : (∀ q, Function.Exact …) ∧ (∀ q, IsStrict …) ∧ (∀ q, IsClosed
(range …))` — **Lemma 5.1 clauses 1–3**; `theorem exists_d1_lift_pow … (r) : ∃ h : ℕ, ∀ x ∈
Ideal.span (Set.range r), ‖x‖ ≤ 1 → …` and `pow_smul_graphIdeal_inter_unitBall_subset … : ∃ h, (fun
x => polyToP (C t) ^ h * x) '' (…) ⊆ …` — **eq. (9)**; `exists_d2_lift_pow`,
`pow_smul_ker_d1_inter_subset` — **eq. (10)**.

**`FJP/Over/JetRings.lean`** (K8a, namespace `FiniteJetOver`). `abbrev JetC := PowerSeries.Restricted
(L K) 1`, `abbrev JetB := DualNumber (PowerSeries.Restricted K 1)`, `abbrev JetD := DualNumber (L K)`,
`abbrev JetA := ↥(jetSupport K)`; `theorem milnorRow_exact`; uniformizer family `noncomputable def
piA/piB/piC/piD (ϖ : Uniformizer K)`; Huber/Tate instance stack.

**`FJP/Over/UniformDomain.lean`** (K8b, namespace `FiniteJetOver`). `theorem isUniform_JetA (ϖ) :
TopologicalRing.IsUniform (JetA K)`; `theorem not_isNoetherianRing_JetA : ¬ IsNoetherianRing (JetA
K)` (`ker_jB_not_fg`); the `not_isUniform_JetB` witness (needs only `0<‖ϖ‖<1`).

**`FJP/Over/Chart.lean`** (K8c, namespace `FiniteJetOver`). the `(W;ϖ)`-chart
(`rescaleRestricted`, `chartDatum`, `not_isUniform_chart`); `theorem not_isStablyUniform_JetA (ϖ)
[IsHuberRing (JetA K)] : ¬ TopologicalRing.IsStablyUniform (JetA K)`.

**`FJP/Over/StrictLocalization.lean`** (K8d, namespace `FiniteJetOver`). rational-localization /
strictness layer feeding sheafiness: `theorem extRhoC_strict_surjective`;
`isNoetherianRing_restricted_L (ϖ)`, `isNoetherianRing_unitBall_restricted_L (ϖ)`;
`mapRestricted_polyToP`.

**`FJP/Over/Functoriality.lean`** (K8d, namespace `FiniteJetOver`). rational-datum functoriality to
the B/C/D vertices: `def pushDatumB/pushDatumC/pushDatumD (D : RationalLocData (JetA K)) (hD :
D.IsRational)` with `_isRational`; `noncomputable def presheafValueMapB/C/D` with `_continuous`,
`_canonicalMap`.

**`FJP/Over/SheafTransfer.lean`** (K8d, namespace `FiniteJetOver`). `theorem gluing_JetA … : ∃ x :
presheafValue C.base, ∀ D : ↥C.covers, restrictionMap … x = f D` (the glued section;
`maxHeartbeats 6400000`); `theorem isSheafy_JetA (ϖ)(hK₀) : ValuationSpectrum.IsSheafy (JetA K)`;
`theorem isSheafy_JetA_of_dvr [IsDiscreteValuationRing 𝒪[K]] : IsSheafy (JetA K)`.

**`FJP/Over/SheafyEndpoints.lean`** (K9, namespace `FiniteJetOver`). the public Theorem-1.3 family in
two layers (explicit ϖ + `_of_dvr`): `finiteJet_isUniform`, `finiteJet_isDomain`,
`finiteJet_not_noetherian`, `finiteJet_not_stablyUniform`, and the real structure presheaf
`finiteJet_structurePresheaf_isSheaf_all (ϖ)(hK₀)(Bplus : RingOfIntegralElements (JetA K)) : … IsSheaf …`,
`finiteJet_structurePresheaf_isSheafOfTopologicalRings_all`,
`finiteJet_completionModel_structurePresheaf_isSheaf(_OfTopologicalRings)`, `finiteJet_structureSheaf`,
plus all `_of_dvr` counterparts.

**`FJP/Over/ExamplePadic.lean`** (K11, namespace `FiniteJetOver.Padic`). `instance
instIsDiscreteValuationRing : IsDiscreteValuationRing 𝒪[ℚ_[p]]` (via
`IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (integerRingEquiv p)` from `ℤ_[p]`);
`padicFiniteJet_isUniform/_isDomain/_not_noetherian/_not_stablyUniform/_isSheafyTateRing/`
`_isSheafyFor_all/_isSheafyComplete`; presheaf regression
`padicFiniteJet_structurePresheaf_isSheaf_all (Bplus) : … IsSheaf …` (+ `…isSheafOfTopologicalRings_all`,
`…completionModel…`) — all at `K = ℚ_[p]`.

**`FJP/Over/LaurentCompat.lean`** (K10, namespace `FiniteJet.Compat`). `theorem jetA_eq :
FiniteJetOver.JetA (LaurentSeries F) = FiniteJet.JetA F := rfl` (the defeq bridge);
`powerSeriesEquivUnitBall`, `powerSeriesEquivInteger`; and the **five recovered wrappers**
`finiteJet_isSheafy`, `finiteJet_isUniform`, `finiteJet_isDomain`, `finiteJet_not_noetherian`,
`finiteJet_not_stablyUniform` — each a one-line specialisation of the generic `FiniteJetOver`
endpoint, matching the frozen `FiniteJetMain.lean` statements.

## 10. Commit range + stats

`git log --oneline 79f069da0..HEAD` — **15 commits** (K0 → K11; prompt's "17" is an overcount, the
range holds 15):

```
ae4a1ef57 FJP-CDVF Phase 3/9 (K10): Laurent compatibility wrappers; frozen five recovered as specializations
871958150 FJP-CDVF Phase 3/9 (K11): p-adic regression — the independent CDVF witness
7ba853560 FJP-CDVF Phases 7+8 (K6+K7): strictness, closed images, and equations (9)/(10) — Lemma 5.1 complete
ac4b7a2b7 FJP-CDVF Phase 9 (K9): general public FJP endpoints over a CDVF base
5d4ee5ef0 FJP-CDVF Phase 3 slice d (K8d): the sheafiness engine over a CDVF base
ac3d97fa5 FJP-CDVF Phase 6 (K5): all-degree exactness over the restricted Tate algebra by flat base change
d270c94c7 FJP-CDVF Phase 5 (K4): all-degree polynomial graph-Koszul exactness
bdb8626fe FJP-CDVF Phase 3 slice c (K8c): generic (W;varphi) chart and non-stable-uniformity
4ca717095 FJP-CDVF Phase 2 complete (K2b+K2c): RestrictedGaussAdic extraction + strong noetherianity
04b0b8ac4 FJP-CDVF Phase 3 slice b (K8b): generic uniform/domain/non-noetherian layer; drop unused discreteness
7c35d9ae7 FJP-CDVF Phase 4 (K3): finite-free Koszul complex in all degrees
9f9ad0429 FJP-CDVF Phase 3 slice a (K8a): generic Milnor-square jet rings over a CDVF base
f4b8e6cbe FJP-CDVF Phase 2a (K2a): noetherianity of principal-ideal adic completions
50159e02b FJP-CDVF Phase 1 (K1): two-layer CDVF base-field API
922689ffa FJP-CDVF Phase 0: paper Lemma 5.1 extraction, codebase inventory, crosswalk + ticket decomposition
```

`git diff --stat 79f069da0..HEAD | tail -1`:

```
 25 files changed, 11663 insertions(+), 687 deletions(-)
```

22 `.lean` files + 3 Phase-0 process docs (`crosswalk.md`, `paper-lemma51-extraction.md`,
`codebase-inventory.md`, all under `.mathlib-quality/fjp-cdvf/`, dev-branch only).

---

**Campaign complete. All 10 acceptance gates pass. FJP is sorry-free and axiom-clean
(`{propext, Classical.choice, Quot.sound}`); the five frozen Laurent headliners are byte-identical
and recovered as specialisations; the whole tree and the `«Adic spaces»` umbrella build green.**
