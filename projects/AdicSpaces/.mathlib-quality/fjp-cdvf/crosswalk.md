# FJP → CDVF campaign — Phase 0: design decisions, crosswalk, ticket decomposition

Branch `fjp/cdvf-lemma51`, worktree `/Users/mcu22seu/Documents/GitHub/aintlib-adic-fjp`,
base HEAD `79f069da0` (dev/adic-spaces). Companion documents in this directory:
`paper-lemma51-extraction.md` (statement faithfulness source of truth),
`codebase-inventory.md` (declaration inventory, Laurent-specificity map, import graph).

## Ground rules (from the handover; binding)

- FROZEN literally: the five `FiniteJet.finiteJet_*` types in **`FJP/FiniteJetMain.lean`**
  (isSheafy / isUniform / isDomain / not_noetherian / not_stablyUniform). Old Laurent API
  becomes thin specializations — no removals, no mass renames.
- No new `sorry`/`admit`/`axiom`/`unsafe`/opaque assumption packaging the conclusion. FJP
  stays sorry-free. `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}; **never sorryAx**
  (in particular: do NOT import/use `AdicCompletionNoetherian.isNoetherianRing` — sorried).
- No `IsNonarchimedeanLocalField` (adds local compactness/finite residue field). No public
  class assuming `IsStronglyNoetherian K` / `∀ m, IsNoetherianRing (unitBall (P K m))` —
  those are Phase-2 CONCLUSIONS. Internal uniformizer-bundling structures OK.
- No discrete topologies in the sheaf argument. No hidden `NeZero m`.
- Do not reopen `isSheafy_of_stronglyNoetherian_828b` (done, general).
- Commit coherent phases separately on `fjp/cdvf-lemma51`.

## Key discoveries shaping the design

1. **`GraphKoszul` is already fully generic** (zero Jet/Laurent mentions): `P E m`,
   `polyToP`, `translationEquiv`, `syzygy_graph_polynomial`, `ballAdicEquiv`,
   `flat_polyToP`, `syzygy_graph_restricted`, `isClosed_graphIdeal` (arbitrary `r`!),
   `exists_d1_lift`, `exists_d2_lift`, `exists_lift_norm_le_of_closed_range` — all over
   abstract `E` + explicit scaling bundle `(t, htu, ht1 : ‖t‖<1, ht0 : 0<‖t‖, hscale)`.
   The campaign EXTENDS this file's degree-1/2 layer to all degrees; the base-field work
   (Phase 1) only needs to FEED its existing `(t,…)` interface.
2. Laurent-specific material is exactly: `FiniteJetRings` norm_K_discrete (53–69) +
   uniformizer block (535–789); `FiniteJetNoetherianVertices.isNoetherianRing_unitBall_gaussK`
   (362–394, the Psi transposition — genuinely K = F((t))) + `IsStronglyNoetherian K`
   consumption (160–196); `FiniteJetUniformDomain.not_isUniform_JetB` witness (403–426,
   needs only 0<‖t‖<1); all of `FiniteJetChart` (the (W;ϖ)-chart, by design;
   `rescaleRestricted` generic). `RestrictedLaurent.lean` is FULLY generic already;
   `norm_mul_eq`'s discreteness hypothesis `_hd` is unused (drop it).
3. Mathlib (pinned): NO Koszul complex (3 comment hits only). NO adic-completion
   noetherianity; `MvPowerSeries` noetherianity is a TODO. HAS: `R⟦X⟧` noetherian instance
   (`PowerSeries/Ideal.lean:196`), `AdicCompletion.flat_of_isNoetherian`,
   `AdicCompletion.map_exact`, root-level `exact_of_localized_maximal`
   (`LocalProperties/Exactness.lean:119`, maximal ideals suffice), `Module.Flat.lTensor_exact`
   (M explicit, maps strict-implicit), `TensorProduct.piScalarRight` (LinearEquiv form at
   `LinearAlgebra/TensorProduct/Pi.lean:165`, needs `[Fintype ι] [DecidableEq ι]`),
   `LinearEquiv.conj_exact_iff_exact`, full DVR/uniformizer API
   (`IsDiscreteValuationRing.exists_irreducible`, `Valued.integer.norm_irreducible_lt_one/_pos`,
   `Valued.integer.mem_iff` — all need `open scoped NormedField` for `𝒪[K]`), DVR ⇒
   noetherian via instances. ℚ_p: NontriviallyNormedField/IsUltrametricDist/CompleteSpace +
   `IsDiscreteValuationRing ℤ_[p]`; `𝒪[ℚ_[p]]` needs a `Subring`-ext bridge +
   `RingEquivClass.isDiscreteValuationRing`. LaurentSeries: mathlib has NO normed-field
   instance (project supplies its own; locate at Phase 3).
4. Frozen-endpoint correction: the five Theorem-1.3 headliners live in `FiniteJetMain.lean`;
   `FiniteJetSheafyEndpoints.lean` holds the *_all / completion-model / TateRing endpoints
   (types quoted in `codebase-inventory.md` §3).

## Design decisions

- **D1 (base stack).** `variable (K) [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]`; `open scoped NormedField` for `𝒪[K]`. Layer 1: explicit
  `(ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)`; internal bundle `structure Uniformizer K` (fields:
  ϖ, irreducible — NOTHING noetherian). Layer 2: `[IsDiscreteValuationRing 𝒪[K]]` chooser
  via `exists_irreducible`. Derived (never assumed): ϖ ≠ 0, `IsUnit (ϖ : K)`,
  `0 < ‖ϖ‖ < 1`, powers → 0 / `IsTopologicallyNilpotent`, `‖ϖ^h * x‖ = ‖ϖ‖^h * ‖x‖`
  (norm_mul + norm_pow), `IsNoetherianRing 𝒪[K]` (inferInstance via PID),
  `unitBall K ≃+* 𝒪[K]` bridge (`mem_unitBall_iff` ↔ `Valued.integer.mem_iff`), and the
  GraphKoszul scaling bundle for the image of ϖ in K.
- **D2 (noetherian pods).** New clean theorem, principal case only:
  `isNoetherianRing_adicCompletion_span_singleton [IsNoetherianRing R] (a : R) :
  IsNoetherianRing (AdicCompletion (Ideal.span {a}) R)` via the surjection
  `R⟦X⟧ →+* AdicCompletion (span {a}) R`, `X ↦ a` (coefficients: partial sums
  `Σ_{n<k} cₙaⁿ mod (a)^k` form a compatible family; surjectivity by telescoping
  representatives). Avoids the sorried multivariate file entirely. Then:
  `𝒪[K]` noeth → `MvPolynomial (Fin m) (unitBall K)` noeth (instance) → completion noeth
  (new theorem; `I0 = span {C ⟨ϖ,…⟩}` IS principal) → transport along `ballAdicEquiv`
  → `IsNoetherianRing (unitBall (P K m))` → `P K m` noetherian (localization sandwich as
  in `flat_polyToP`) → `IsStronglyNoetherian K`.
- **D3 (Koszul model).** `KoszulIndex m q := {I : Finset (Fin m) // I.card = q}`,
  `KoszulTerm R m q := KoszulIndex m q → R`,
  `koszulDifferential r q : KoszulTerm R m (q+1) →ₗ[R] KoszulTerm R m q`,
  `(d_q x)_J = Σ_{i ∉ J} (-1)^{#{j ∈ J | j < i}} * r i * x_{J ∪ {i}}`.
  SIGN CHECK (done on paper, must be re-done in Lean as conjugation lemmas): for q=1 this
  yields `(d x)_{k} = Σ_{i<k} r_i x_{{i,k}} − Σ_{i>k} r_i x_{{k,i}}`, matching
  `GraphKoszul.d2` (`d₂(e_i∧e_j) = r_i e_j − r_j e_i`, i<j) under
  `Pairs m ≃ KoszulIndex m 2`; for q=0, `d1 = Σ u_i r_i` under `KoszulIndex m 1 ≃ Fin m`.
  Positive-degree exactness = `∀ q, Function.Exact (koszulDifferential r (q+1))
  (koszulDifferential r q)` — exactness at K_{q+1}; NEVER at K_0.
- **D4 (file placement).** `FJP/KoszulFiniteFree.lean`: mathlib-only imports (pure linear
  algebra + topology for `koszulDifferential_continuous` over a topological ring with
  product topologies). Degree-0/1/2 equivalences + conjugations to d1/d2 are APPENDED to
  `FiniteJetGraphKoszul.lean` (which gains `import …KoszulFiniteFree`) — d1/d2 statement
  types stay untouched. `FJP/RestrictedGaussAdic.lean` (K2b): extract the AdicBridge
  block (`P` … `ballAdicEquiv` … `flat_polyToP`, GraphKoszul 1158–1592) upstream; re-home
  `finsupp_prod_one` + the `NormOneClass (MvPowerSeries.Restricted …)` instance (the only
  genuine NoetherianVertices content GraphKoszul uses); GraphKoszul then imports
  RestrictedGaussAdic and NOT NoetherianVertices; `Wedhorn.isClosed_ideal_of_noetherian`
  imported directly from `NoetherianTateModules`. The two
  `set_option backward.isDefEq.respectTransparency false` sites travel with their decls.
- **D5 (all-degree polynomial exactness).** Base lemma: coordinate-sequence exactness
  `∀ q, Exact (koszulDifferential (X ·) (q+1)) (koszulDifferential (X ·) q)` over an
  ARBITRARY CommRing, by induction on m splitting `KoszulIndex (m+1) q` by membership of
  the last variable (mapping-cone block identification; `finSuccEquiv` on coefficients).
  Graph sequence: localize at maximal ideals (`exact_of_localized_maximal`); case
  r_j ∉ 𝔪 → insertion homotopy `(h_j x)_J = (sign) r_j⁻¹ x_{J.erase j}`-style in the
  subset model with `d h + h d = id`; case all r_i ∈ 𝔪 → `1 = a₀g + Σ aᵢfᵢ` makes g a
  unit locally (`g(a₀ + Σ aᵢTᵢ) = 1 + Σ aᵢrᵢ`), translate by `translationEquiv` (exists),
  reduce to unit·coordinate sequence. This follows the PRINTED proof; if a localization
  API obstruction forces the degree-by-degree multiplier-ideal fallback
  (`syzygy_graph_polynomial`-style), that is a REPORTABLE proof-method divergence.
- **D6 (flat transfer).** `K_q(P) = K_q(E[T]) ⊗ P` via `TensorProduct.piScalarRight`
  (Fintype/DecidableEq on `KoszulIndex m q` — derive instances) + `koszulDifferential_map`
  naturality; transfer exactness by `Module.Flat.lTensor_exact` with `flat_polyToP`
  (generic, exists). NOT the degree-1 equational-criterion argument.
- **D7 (strict/closed, all degrees).** d₁ image closed: existing `isClosed_graphIdeal`.
  Higher d_q: im d_q = ker d_{q−1} (exactness) closed by continuity + T2. Strictness:
  `exists_lift_norm_le_of_closed_range` (generic OMT with constants, exists) per
  differential; bridge lemma to `IsStrictLinearMap` (`NoetherianTateModules.lean:57`).
  Headline `koszulGraph_exact_strict_closed` (docstring cites paper Lemma 5.1 clauses 1–3;
  full-5.1 claim only together with K7's (9)/(10)).
- **D8 ((9)/(10)).** From `exists_d1_lift`/`exists_d2_lift` constants C: choose
  `h` with `‖ϖ‖^h * C ≤ 1`; scale. Two statement forms each, per the handover: the
  ∃-h/∀-x norm form AND the lattice-inclusion form
  `ϖ^h • (J_E ∩ P_{E,0}) ⊆ d1(P_{E,0}^m)` (sets inside `P E m`, `P_{E,0}` = `unitBall`),
  identified via `mem_unitBall_iff`. (10) proved generically for qualifying E, specialized
  to D. (9) about the ALGEBRAIC image (extraction §6 caution 1).
- **D9 (generic core).** Namespace `FiniteJetOver`, files `FJP/Over/…` mirroring the
  Laurent development: rings (L K = RestrictedLaurent K — already generic; JetB/C/D/A over
  K with the support-subring model preserved), milnor row (κ=ρ=1 lemmas), uniform/domain,
  non-noetherian, chart at ϖ (`rescaleRestricted` generic), strict localization,
  functoriality, sheaf transfer, endpoints. Old `FiniteJet` namespace: specializations at
  `K = LaurentSeries F` (locate the project's NormedField instance for LaurentSeries during
  the port). `not_isUniform` witness generalizes verbatim (needs 0<‖ϖ‖<1 only).
- **D10 (regression).** `FJP/Over/ExamplePadic.lean`: instantiate the generic endpoints at
  `K = ℚ_[p]` (`𝒪[ℚ_[p]]` DVR via subring-congr bridge from `ℤ_[p]`). This is acceptance
  gate 7's "genuinely independent" witness.

## Paper ↔ Lean crosswalk (targets; names final unless noted)

| Paper item | Lean target (new unless "exists") |
|---|---|
| base field k, k°, ϖ | `[NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]`, `𝒪[K]`, `Uniformizer K` (K1) |
| L₀, B₀, C₀, D₀, A₀ (§1) | exists: `unitBall (L/JetB/JetC/JetD/JetA)`; generic: `FiniteJetOver` versions (K8) |
| P_E, P_{E,0} (§5.1) | exists: `GraphKoszul.P E m`, `unitBall (P E m)` |
| r_i = gT_i − f_i, d_{1,E}, J_E (eq. 2) | exists: `GraphKoszul.d1`, `Ideal.span (range r)`; subset-model `koszulDifferential` (K3) |
| K_{P_E}(r) exact in positive degrees (5.1.1) | `koszulGraph_restricted_exact : ∀ q, Function.Exact (koszulDifferential r (q+1)) (koszulDifferential r q)` (K5) |
| every differential strict (5.1.2) | `koszulDifferential_isStrict` (+ `IsStrictLinearMap` bridge) (K6) |
| every image closed (5.1.2) | `isClosed_range_koszulDifferential` (K6) |
| J_E closed (5.1.3) | exists: `GraphKoszul.isClosed_graphIdeal` |
| eq. (9) | `exists_d1_lift_pow` (∃h norm form) + `pow_smul_graphIdeal_inter_subset` (lattice form) (K7) |
| eq. (10) | `exists_d2_lift_pow` + `pow_smul_ker_d1_inter_subset` (lattice form; generic E, specialized D) (K7) |
| noetherian vertices (asserted §5.1) | K2: `isNoetherianRing_adicCompletion_span_singleton` → `isNoetherianRing_unitBall_P` → `IsStronglyNoetherian K` |
| Thm 1.1 endpoints, general K | K9: `FiniteJetOver.finiteJet_*` family incl. `structurePresheaf_isSheaf_all` (real presheaf, projective-limit topology) |
| Thm 1.1 endpoints, Laurent | FROZEN, exist in `FiniteJetMain.lean` — become 1-line specializations (K10) |

## Tickets

| # | Phase | Content | Depends on | Status |
|---|---|---|---|---|
| K0 | 0 | this crosswalk + the two scout docs, committed | — | done when committed |
| K1 | 1 | `FJP/CDVFBase.lean`: two-layer uniformizer API + derived facts + `unitBall K ↔ 𝒪[K]` bridge + GraphKoszul scaling-bundle feeder | — | **dispatch now** |
| K2a | 2 | `FJP/AdicCompletionPrincipal.lean`: `R⟦X⟧ ↠ AdicCompletion (span {a}) R`, noetherianity | — | **dispatch now** |
| K2b | 2 | `FJP/RestrictedGaussAdic.lean`: extract AdicBridge from GraphKoszul (import-cycle fix) | K3 lands first (same file) | queued |
| K2c | 2 | `IsNoetherianRing (unitBall (P K m))`, `P K m`, `IsStronglyNoetherian K` from D2 chain | K1, K2a, K2b | queued |
| K3 | 4 | `FJP/KoszulFiniteFree.lean` (mathlib-only) + conjugation section appended to GraphKoszul; edge cases m=0/1, q>m; sign tests | — | **dispatch now** |
| K4 | 5 | coordinate all-degree exactness (induction on m) + graph localization → polynomial all-degree exactness | K3 | queued |
| K5 | 6 | flat transfer to `P E m` (lTensor_exact + piScalarRight conjugation), noetherian-pod E | K3, K4, K2 | queued |
| K6 | 7 | closed images + strictness all degrees + headline | K5 | queued |
| K7 | 8 | equations (9)/(10), both forms | K6 | queued |
| K8 | 3 | `FiniteJetOver` generic core (rings→…→sheaf transfer→endpoints), ϖ-parametric chart | K1 (K2c for sheafy pieces) | queued |
| K9 | 9 | general public endpoints incl. structure-presheaf (all A⁺, completion models) | K6, K7, K8 | queued |
| K10 | 3/9 | Laurent compatibility wrappers; five frozen types byte-checked | K8, K9 | queued |
| K11 | 3 | `FJP/Over/ExamplePadic.lean` p-adic regression | K8 (K9 for endpoints) | queued |
| K12 | — | acceptance sweep: axiom audit, added-line scan, targeted + umbrella builds, `git diff --check`, final report | all | queued |

## Risk register

- R1: K2a inverse-limit plumbing (`AdicCompletion` subtype encoding) is fiddly — the
  project's sorried file died on exactly the multivariate version of this. Principal +
  univariate is genuinely easier; if it still jams, fallback = discharge the two sorries
  in `AdicCompletionNoetherian.lean` (then audit) — either path must end sorryAx-free.
- R2: K4's mapping-cone induction is the largest new pure-math piece; the insertion
  homotopy in the subset model needs careful sign bookkeeping (the two paper formulas in
  extraction §4 are normative).
- R3: K8 is the bulk port; mitigated by the inventory's finding that most files are
  already datum-parametric/generic — the port is mostly re-parameterization
  (K, ϖ) + instance plumbing.
- R4: `Valued`/`NormedField` scoped-instance friction (`open scoped NormedField`) and the
  `unitBall` vs `𝒪[K]` carrier split — settle once in K1, everything downstream uses the
  K1 bridge.
- R5: v4.33 `backward.isDefEq.respectTransparency` walls near `toAdic`/`syzygy_graph_restricted`
  — preserve the existing set_option sites when extracting (K2b).
