# Decomposition — the 4 residual leaves of Thm 8.28(b) (sheafiness)

**Mode:** `/develop --decompose` adversarial. **Sources:** all local in `references/`
(`wedhorn.txt`, `huber1.txt`=[Hu1] Habilitation, `huber1994.txt`=[Hu3], BGR, Henkel PDFs).
Source mapping verified against Wedhorn's bibliography (`wedhorn.txt:5725-5745`), NOT memory:
**[Hu1]** = Bewertungsspektrum (Habilitation), **[Hu2]** = Continuous valuations (1993),
**[Hu3]** = A generalization (1994). Build is green (3190 jobs); these are the only
critical-path sorries.

## ★★★★ T-PB cluster (2026-07-03, /develop --continue): carrier #1 power-bounded reroute

**Target**: kill `RationalLocData.completedPlusSubringBase_isBounded` (Presheaf, the B2
over-strong uniform-boundedness sorry — the ONLY sorry carrier of the IRIE
`subset_powerBounded` field, and the bottleneck of the LL valuative criterion
`isPowerBounded_of_forall_vle_one_spa_of_complete`). Skeleton landed (15 `:= by sorry`
decls, build green); ticket board section "T-PB cluster" in `tickets.md`.

### Plain-English proof (Wedhorn's own, transcribed)

`𝒪_X(D)⁺` is by construction the integral closure (in the completion `B = 𝒪_X(D)`) of
`Ĉ₀ = closure(image of C)`, `C = (A⁺[T/s])^int ⊆ Aₛ`. To see `𝒪_X(D)⁺ ⊆ B°` (Wedhorn Def
7.14's third axiom, via Prop 7.19), it suffices — since `B°` is integrally closed in `B`
(Prop 5.30(4)) — to show `Ĉ₀ ⊆ B°`. The generators of `A⁺[T/s]` are power-bounded in `Aₛ`
(`A⁺ ⊆ A°` maps to power-bounded elements; `t/s` lies in the ring of definition
`A₀[T/s]`, which is bounded), so `A⁺[T/s] ⊆ (Aₛ)°` (Lemma 7.20's content); its integral
closure `C` stays in `(Aₛ)°` by Prop 5.30(4) at `Aₛ`; the completion coercion carries
power-bounded to power-bounded (7.47(1) direction); and `B°` is closed (it contains the
open subring `closure(image A₀[T/s])`, hence is an open, therefore closed, subgroup), so
the closure `Ĉ₀` of the image of `C` stays in `B°`. Finally an element of `𝒪_X(D)⁺` is
integral over `Ĉ₀ ⊆ B°`, hence power-bounded by Prop 5.30(4) at `B`.

### Verbatim source quotes

- **Prop 7.19** (wedhorn.txt:3015–3029, p. 61): "Let A = (A, A⁺) be an affinoid ring and
  let (Tᵢ) be a finite family of subsets of A such that Tᵢ·A is open for all i. Then
  (A⟨X⟩_T, (A⁺⟨X⟩)^int) is an affinoid ring […] **Proof.** As A⁺ is open in A, then A⁺⟨X⟩
  is open in A⟨X⟩_T. Hence (A⁺⟨X⟩)^int is open. It remains to show that (A⁺⟨X⟩)^int is
  contained in A⟨X⟩°_T. As A⟨X⟩°_T is integrally closed in A⟨X⟩_T, it suffices to show
  that A⁺⟨X⟩ is contained in A⟨X⟩°_T. This follows from the following lemma."
- **Lemma 7.20** (wedhorn.txt:3031–3040, p. 61): "Let A be a f-adic ring and let (Tᵢ) be a
  family of subsets of A such that Tᵢ·A is open in A for all i. Then (A°)⟨X⟩ ⊆ (A⟨X⟩_T)°.
  […] **Proof.** Let a ∈ (A°)⟨X⟩ and write a = b + c, where b ∈ (A°)[X] and c ∈ J⟨X⟩,
  where J is an ideal of definition of A. Then b and c are both power-bounded. Therefore
  a is power-bounded."
- **Prop 5.30** (wedhorn.txt:1786–1804, p. 37): "Let A be a non-archimedean topological
  ring. […] (2) A subset T of A is power-bounded if and only if the subring of A generated
  by T is bounded. (3) The union of all bounded subrings is A°, and this is a subring of A.
  (4) A° is integrally closed in A […] **Proof.** […] It remains to show (4). Let a ∈ A be
  integral over A°. By (3), a is integral over a bounded subring B of A. Therefore there
  exists an integer N such that B[a] = B + Ba + ··· + Ba^{N−1}. Thus B[a] is bounded and
  hence a is power-bounded."

### Lean ↔ source match

The project models `A⟨T/s⟩` as `presheafValue D` = completion of `Aₛ` with the
localization topology; Wedhorn's `A⁺⟨X⟩` (closure of the image of `A⁺[X]` under
`X ↦ t/s`) corresponds to `closure(coeRingHom '' locPlusSubring)`; his `(·)^int` is taken
in the completion (project Def: `completedPlusSubring = IntCl_B(Ĉ₀)`, making
integral-closedness free — Wedhorn instead cites [Hu1] 2.4.3 to move `^int` across the
completion; the two agree, and our form needs only the CONTAINMENT direction proven here).
Wedhorn's proof-by-decomposition `a = b + c` (polynomial part + `J⟨X⟩` tail, "both
power-bounded") is packaged in the skeleton as: image-of-`C` power-bounded (the `b` part,
T-PB10/11/12) + closedness of `B°` absorbing the completion tail (the `c` part, T-PB6/14) —
the same content, organized around `closure_minimal` instead of an explicit series split.
Prop 5.30 is stated by Wedhorn for **plain nonarchimedean topological rings**; the
skeleton's Bounded.lean layer (T-PB1–6) keeps exactly that generality (pair-free), unlike
the earlier pair-carrying `PairOfDefinition.isPowerBounded_of_monic_powerBounded_eval`
(which stays; the pair-free form is needed at `B` where no pair exists upstream of
Presheaf.lean).

### Leaves (all stated `:= by sorry`, file:line in tickets.md table)

Each leaf's discharge, per Step 4: T-PB1/2/3/4/5/6 — mathlib + existing project engines
(`IsBounded.isPowerBounded_of_isIntegral` Bounded:386 ✓ exists, `isBounded_adjoin`
induction HuberRings:639 ✓ exists to crib, `image_closure_subset_closure_image`,
`AddSubgroup.isClosed_of_isOpen` — mathlib names to re-verify at execution);
T-PB7/8/9 — existing locNhd machinery (`locNhd_invS_mem`'s `Submodule.span_induction`
pattern LocTop:148 ✓, `Ideal.map_pow`, `Ideal.mul_mem_left`); T-PB10–15 — compositions of
the above with in-file patterns (Presheaf:1489 `hag_loc`, Presheaf:649 `hasBasis` openness
proof ✓ all exist); T-PB16/17 — rewiring + deletion, no new math.

### Attacks attempted (adversarial pass, per leaf group)

- **T-PB1 (⊥ bounded).** [1] Counterexample: `ℝ_std` — `ℤ·1` unbounded; hypothesis
  `[NonarchimedeanAddGroup]` is necessary and present ✓ (matches Wedhorn 5.30's standing
  nonarch hypothesis). [2] Edge: char p — `⊥` finite, trivially bounded; char 0 — infinite
  but `n·v ∈ G` for `v ∈ G` open subgroup ✓. [3] Hypothesis-strength: cannot drop nonarch
  (attack 1); cannot weaken to `T1`/`T2` — irrelevant axes. SURVIVED.
- **T-PB2 (5.30(2) finite).** [1] Source-drift: Wedhorn's (2) is for a *power-bounded
  subset* T (uniformly), not elementwise — for INFINITE elementwise-pb T the statement is
  FALSE (e.g. unbounded scalings); skeleton restricts to `Finset` where elementwise ⟹
  set-pb via `IsBounded.mul` — scope is correct ✓. [2] Discharge: the `isBounded_adjoin`
  induction body (HuberRings:639–706) uses only `[NonarchimedeanRing]`-field
  `is_nonarchimedean` — same field in `NonarchimedeanAddGroup` ✓ replicable upstream.
  [3] Edge: `T = ∅` → `Subring.closure ∅ = ⊥` → T-PB1 ✓. SURVIVED.
- **T-PB3/4 (5.30(4)).** [1] Counterexample search: b2_log has NO entry against 5.30(4)
  (checked 2026-07-03; entries 6/7 concern MvPolynomial-vs-TateAlgebra and pb-transfer
  along arbitrary homs — different statements). [2] Edge: `p = X` (degree 1, coeff 0) →
  `x = 0` pb ✓; `natDegree 0` degenerate → `1 = 0`, everything pb ✓ (the landed HuberRings
  analog handles this case explicitly, :401–406). [3] Discharge: engine
  `IsBounded.isPowerBounded_of_isIntegral` exists sorry-free (Bounded:386, verified today).
  [4] Hypothesis: `[IsTopologicalRing]` needed by the engine; nonarch needed by T-PB2.
  SURVIVED.
- **T-PB6 (closure of bounded).** [1] Attack "closure of elementwise-pb is pb" — that
  STRONGER claim is dubious; the skeleton only claims closure of BOUNDED is bounded, which
  the closed-open-subgroup absorption proves ✓ (`Ḡ = G` for open subgroups). [2] Order of
  multiplication: `IsBounded` is `S * V ⊆ U` (S left); fixed-`v` continuity argument works
  on the left factor ✓. [3] Nonarch necessary: in `ℝ`, closure of a bounded set is bounded
  too — but our proof needs closed absorbing nbhds; nonarch supplies them; keeping the
  hypothesis is harmless (all consumers are nonarch). SURVIVED.
- **T-PB7/8/9 (localization transfer).** [1] The prior-B2 attack (b2_log entry 7:
  `IsPowerBounded.map` FALSE for arbitrary continuous homs — counterexample
  `id : ℝ_disc → ℝ_std`): our statements are NOT the generic transfer — they are specific
  to `algebraMap` with the `locTopology` built from the SAME pair `P`, where `locNhd`
  absorption is available; the counterexample does not embed (its target topology is not a
  locTopology of the source's pair). Addressed ✓. [2] Composition attack on T-PB8's chain
  `(I^m-image)·S ⊆ I^n-image` uses A-boundedness of S against the P-adic basis — P's basis
  IS A's nbhd basis (PairOfDefinition contract) ✓. [3] Edge: `S = ∅`/`{0}` trivial ✓;
  `s` nilpotent → `Localization.Away s` trivial ring, everything bounded ✓. SURVIVED.
- **T-PB10–15 (assembly).** [1] Composition: could all pieces hold and
  `completedPlusSubringBase ⊆ B°` fail? `base = closure(image(IntCl))`;
  `closure_minimal` needs image ⊆ `B°` (T-PB11∘T-PB12 pointwise ✓) and `B°` CLOSED
  (T-PB14) — no gap. [2] T-PB14's "A° contains an open subring ⟹ open": needs A° to be a
  SUBRING (add-closed) — supplied by `powerBoundedSubring.toSubring` which needs
  `[NonarchimedeanAddGroup B]` = T-PB13 ✓ (dependency recorded). [3] Vacuity: is
  `completedLocSubring` actually open? Its openness proof is the same locNhd-1 absorption
  as `completedPlusSubringBase_isOpen` (landed a3808076) with the TRIVIAL containment
  `locNhd 1 ⊆ locSubring` (subtype image of an ideal of the subring) — strictly easier ✓.
  [4] Instance-diamond attack on `@powerBoundedSubring _ _ D.topology` vs the completion's
  global instances: A_s-level statements use explicit `@`-form with `D.topology` (the
  file's established idiom, cf. :4010), completion-level use the global `presheafValue`
  instances — no mixing in any single statement ✓. SURVIVED.
- **T-PB16 (retarget).** [1] Could the field's OLD proof shape not match: the existing
  body derives `hx_int : IsIntegral ↥base x` then applies the bounded engine — the new
  route consumes the SAME `hx_int` via T-PB4 with `hB := T-PB15` — signature-compatible ✓.
  [2] Hidden-hypothesis attack: T-PB16 adds NO new binders to the instance (T-PB13 is
  `haveI`-internal) — headline signature unchanged ✓ (the §8.4 leak test).
- **Prior-B2 log consultation** (Step 4.6): entries checked 2026-07-03. Entry 7
  (`IsPowerBounded.map`) — addressed at T-PB7/8/9 attack [1] above (specialized true
  forms). The 2026-06-24 route-divergence B2 (uniform IsBounded over-strong) is the very
  statement this cluster REPLACES (T-PB17 logs its resolution). No other name/shape match.

### Confidence gate

All leaves: mathlib/project-discharged or composition-of-skeleton (no API gaps); skeleton
compiles (build green, sorries only — verified 2026-07-03); every leaf has the quotes above
(Prop 5.30 / 7.19 / 7.20 with line refs into wedhorn.txt); adversarial pass recorded; no
REVIEW-PENDING. GATE PASSES for the T-PB subtree.

## ★★★ ADVERSARIAL DECOMPOSE round 3 (2026-06-20) — the T-L1c inducing assembly (read FIRST)

Target: the in-WCA `productRestrictionSub_isInducing_via_equalizer` route (reviewer #2's
equalizer+OMT, post the 5 landed topological foundations + the cracked cg-diamond). Disposition:
break the assembly before building it. **VERDICT: SURVIVED — no fatal flaw; every ingredient
verified to exist; the residual is effort (module/ContinuousSMul/OMT plumbing + a headline rewire),
not a gap.**

Decomposition (sub-leaves of the inducing proof):
- **L-A `ContinuousSMul A (presheafValue D)` (+ Pi + E).** The A-action is `a • x = canonicalMap a * x`.
- **L-B `Module A (presheafValue D)` + E as an A-`Submodule`.** Non-ambient `letI` (FlatnessResults
  `RingHom.toModule (canonicalMap D)` pattern) + `Pi.module` + the equalizer submodule.
- **L-C `ρ̃ : R →ₗ[A] E` bijective.** Corestrict `productRestrictionSub` (lands in E via
  `productRestrictionSub_mem_sectionEqualizer`), A-linear; injective = `cor_8_32_…injective`;
  surjective = `lemma_8_34_gluing` (its `hcompat` IS E's membership predicate).
- **L-D OMT → homeo → inducing.** `wedhorn_6_16_of_topNilpUnit ϖ … ρ̃` → `IsOpenMap` →
  continuous+bijective+open ⇒ homeo → `ρ = subtypeVal ∘ ρ̃` inducing.
- **L-E headline rewire.** `embedding := ⟨L-D inducing, cor_8_32_…injective⟩`.

### Attacks attempted
- **[1] Import-cycle attack (L-E/L-D).** WCA must import `WedhornBanachTheorem` for the OMT.
  CHECKED: `WedhornBanachTheorem` imports only `BanachOMT` + `HuberRings` (upstream); 0 imports of
  StructureSheaf/RPK/WCA/Cor832/GeometricReduction. **No cycle** — the import is safe.
- **[2] Prior-B2 attack.** `b2_log.jsonl` grep for inducing/embedding/equalizer/productRestriction/
  isOpenMap/sectionEqualizer → **empty**. No prior B2 on this assembly.
- **[3] A-linearity attack (L-C, the sharpest).** The OMT needs `ρ̃ : →ₗ[A]`, so `productRestrictionSub`
  must be A-LINEAR w.r.t. the `canonicalMap.toModule` structures — i.e. `restrictionMap (canonicalMap a)
  = canonicalMap a`. CHECKED: **`productRestriction_comp_canonicalMap` (StructureSheaf:1682)** gives
  exactly `productRestriction A C (C.base.canonicalMap a) D hD = D.canonicalMap a`. Coherence EXISTS.
  Attack fails to break it.
- **[4] ContinuousSMul-discharge attack (L-A).** Continuity of `(a,x) ↦ canonicalMap a * x` needs
  `canonicalMap` continuous + `presheafValue` `ContinuousMul`. CHECKED: **`canonicalMap_continuous`
  (PresheafIdentification:888)** + `presheafValue` is a topological ring. Provable (~3 lines); E/Pi via
  `Pi.continuousSMul` + subtype. No gap.
- **[5] OMT-precondition attack (L-D).** `wedhorn_6_16_of_topNilpUnit` needs M,N: AddCommGroup/Module A/
  UniformSpace/IsUniformAddGroup/CompleteSpace/cg/T2/ContinuousSMul + a topNilp unit. M=`presheafValue
  base`, N=`↥sectionEqualizer`: cg ✓ (landed), complete ✓ (landed), T2 ✓, Module/ContinuousSMul (L-A/L-B),
  ϖ ✓ (`IsTateRing.exists_topologicallyNilpotent_unit`). Every precondition is producible.
- **[6] Surjectivity-composition attack (L-C).** Could gluing's output mismatch E's membership? CHECKED:
  `lemma_8_34_gluing`'s `hcompat` hypothesis is the SAME `∀ D₁ D₂ D₃ h₃₁ h₃₂, restrictionMap … = …`
  predicate as `sectionEqualizer`'s carrier (verified earlier, StructureSheaf:311 ↔ WCA:12841). So for
  `e ∈ E`, `lemma_8_34_gluing e.val e.property` gives the global preimage ⇒ `ρ̃` surjective. Matches.
- **[7] Headline-rewire / instance attack (L-E).** The new inducing needs `[CompleteSpace A]
  [CompatiblePlusSubring A]` (from gluing). The headline `isSheafy_of_stronglyNoetherian_828b` HAS both.
  `[CompatiblePlusSubring A]` is on the BASE `A` (Tate, fine — it's false only for COMPLETIONS, which
  this is not). Rewire `embedding := ⟨new_inducing, cor_8_32_…injective⟩` is sound. The upstream
  StructureSheaf `productRestrictionSub_isInducing_tate` sorry becomes orphaned (off the headline path).

**Verdict: the equalizer+OMT inducing route is FEASIBLE and faithful.** All discharges verified against
in-repo decls (`productRestriction_comp_canonicalMap`, `canonicalMap_continuous`, `lemma_8_34_gluing`,
`cor_8_32_…injective`, `wedhorn_6_16_of_topNilpUnit`, the 5 sectionEqualizer foundations). No mathlib
gap, no false leaf, no orphan. Build it in WCA (next `/beastmode`).

---

## ★★ ADVERSARIAL DECOMPOSE round 2 (2026-06-19) — attack logs per leaf (read FIRST)

Disposition: opposing the plan. Each leaf attacked across the 5 categories + prior-B2 log
(`b2_log.jsonl`, 2 entries consulted). Net: **T-L1/T-L2 survive; T-L3 survives + improved
(its feared-deep input is already proven); T-L4 FAILED — it is NOT the trivial wrapper the
reviewer implied.** One decision point for the user (T-L4).

### T-L1 (equalizer + OMT inducing) — VERDICT: SURVIVED, real work itemised
- **[1] Counterexample / discharge attack on the OMT input.** The reviewer said "apply the
  already-formalized Theorem 6.16." FLAW in the naive reading: the landed
  `isOpenMap_of_completeSpace_of_countablyGenerated` carries `[SigmaCompactSpace G]`, with an
  explicit in-file counterexample (ℝ-discrete→ℝ-Euclidean) and a `b2_log` note — **false for the
  Tate `R` of interest.** RESOLVED, not fatal: the correct input is `wedhorn_6_16_of_topNilpUnit`
  (WedhornBanachTheorem:408), σ-compact-free, already used on `f.rangeRestrict` in
  `_sub_lemma_L4_3_strict_via_closed_image`. Ticket pins it.
- **[2] Precondition attack (does the OMT even apply to `ρ̃`?).** `wedhorn_6_16_of_topNilpUnit`
  needs `f : M →ₗ[A] N` (bundled A-linear). **`productRestrictionSub` is an unbundled function
  `presheafValue base → ∀ D, presheafValue D` (StructureSheaf:275), NOT a `→ₗ[A]`.** Real work:
  T-L1b must build `productRestrictionToEqualizer : R →ₗ[A] E` (bundle the existing additive/
  algebra structure). Not fatal, but not free.
- **[3] Precondition attack (cg uniformity on the equalizer).** OMT needs
  `[(uniformity N).IsCountablyGenerated]` on the target. CHECKED: `IsCountablyGenerated
  (uniformity (presheafValue D))` IS established in-repo (LaurentRefinementCore:2689); the
  equalizer `E ⊆ ∏` (finite product) inherits it via `Filter.comap.isCountablyGenerated`
  (the `_sub_lemma_L4_3` pattern). Also need `ContinuousSMul A R`, `ContinuousSMul A E` — to
  verify at build time (plausible; presheafValue is a topological A-algebra).
- **[4] Composition attack (is inducing independent of gluing?).** NO. `IsOpenMap ρ̃` needs `ρ̃`
  **surjective** = the gluing axiom (Leaf C). Alternative (OMT on `ρ.rangeRestrict`) needs
  `range(ρ)` closed = complete; without module-finiteness (the 6.18 route the reviewer rejects),
  `range(ρ)` closed ⟺ `range(ρ) = E` ⟺ gluing. **So T-L1c is genuinely gated on Leaf C.** The
  "4 independent leaves" framing is wrong: the embedding side sits on top of gluing. Board encodes
  this (T-L1b depends on Leaf C); recommended order corrected: Leaf C before T-L1b/c.
- **[5] Source-drift.** `sectionEqualizer_isClosed` (kernel of continuous overlap-diff) is standard
  topology, no Wedhorn proposition mis-cited. ✓
- **Prior-B2:** no name/shape match.

### T-L2 (completion ring of integral elements) — VERDICT: SURVIVED (external leaf in hand)
- **[1] Source-drift on 7.47(4).** CHECKED `wedhorn.txt:3556`: "(4) Rings of integral elements of
  A and rings of integral elements of Â [correspond]. Proof. [Hu1] 2.4.3." Leaf claim matches
  exactly. The external cite is **[Hu1] 2.4.3, which IS in hand** (`huber1.txt`), so this is a real
  sub-development, not unfulfillable infrastructure (CLAUDE.md STOP tell does NOT fire).
- **[2] Discharge attack on the precompletion (7.19/7.20).** The `subset_powerBounded`/openness at
  the *precompletion* level (C = IntCl(A⁺[T/s]) ⊆ (A_s)°, open) needs the 7.20 inclusion
  `(A°)⟨T/s⟩ ⊆ (A_s)°` and `C ⊆ (A°)⟨T/s⟩`. TO VERIFY at build time: the `⟨T/s⟩` (restricted) vs
  `[T/s]` (plain localization) distinction in the in-repo `locPlusSubring`/`Localization.Away`
  encoding — a place a gap could hide. Flagged, not fatal.
- **[3] Definitional-match attack.** Leaf assumes `(presheafValue D)⁺ = closure(coeRingHom C)`. The
  T-ROIE-1 def `completedPlusSubring D := closure((IntCl(locPlusSubring)).map coeRingHom)` matches;
  confirm `(presheafValue D)⁺` resolves to `completedPlusSubring D` (ringPlus instance key).
- **Prior-B2:** the deleted `completedPlusSubring_le_ringOfDef` B2 is about the *false* `Ĉ ⊆ B₀`
  (ring of definition), NOT about `Ĉ` being a ring of integral elements (this leaf). No conflict —
  this leaf is the correct replacement direction.

### T-L3 (analytic Spa point) — VERDICT: SURVIVED + IMPROVED (feared input already proven)
- **[1] Deep-leaf attack (is 7.45 a live sorry?).** Feared T-L3 bottoms at an unproven 7.45.
  CHECKED: **`Lemma745.lean` has 0 sorries** — `exists_spa_point_via_restrictToConvex` (L418) and
  `exists_mem_spa_supp_ge_of_nonOpen_prime` (L691) are PROVEN. The analytic-point existence is DONE.
  Moreover `restrictToConvex` yields a valuation "automatically MulArchimedean (rank ≤ 1)"
  (Lemma745:38) — i.e. the **height-1 property is built in**, so Remark 4.12 generization is not a
  separate deep step.
- **[2] Hypothesis/conclusion-strength attack (b2 shape-match).** `b2_log` entry
  `exists_spa_point_supp_eq_nonOpen_maxIdeal_of_complete` was FALSE for bare `PlusSubring` (A⁺=⊤ ⟹
  Spa(A,⊤)=∅, counterexample A=ℚ_p). **T-L3 dodges it**: T-L3 concludes the bound on
  `powerBoundedSubring A` (A°), which is `A⁺`-INDEPENDENT — NOT on A⁺. The existing Lemma745 lemmas
  conclude the A⁺/A₀-bound (need `A⁺⊆A₀`); T-L3 needs the **A°**-bound, which is STRICTLY STRONGER
  (A₀ ⊆ A°), supplied by **Prop 7.41** (height-1 ⟹ bounded on A°). So T-L3's residual = wire the
  proven height-1 analytic point (Lemma745) + Prop 7.41 (≈ the docstring's 6-line argument, now
  legitimately ≈6 lines because the height-1 point is already in hand) + pair-free plumbing. **More
  tractable than the board's "deep" flag implied.**
- **[3] Source-drift on 7.41.** `wedhorn.txt:3487` (Prop 7.41) is the height-1-analytic ⟹
  bounded-on-A° step; matches. Archimedean value-group API exists in-repo (Presheaf:3331–3438,
  the 7.40(6) chain).
- **Verdict:** ticket sharpened — drop the "7.45 is a deep in-repo sorry" framing; the residual is
  Prop 7.41 + the A₀→A° upgrade + pair-free wiring.

### T-L4 (former leaf #4 = 7.52(1)/7.18(1)) — VERDICT: ⚠ FLAW — NOT a trivial wrapper
- **[1] Discharge attack (is 7.52(1)/7.18(1) actually dischargeable in-repo?).** The reviewer:
  "leaf #4 is essentially trivial via 7.52(1)." FALSE as a formalization claim. The in-repo 7.18
  content is:
  - `isIntegral_of_forall_valuation_le_one` (Presheaf:1569): PROVEN, but quantifies over **ALL**
    valuations (a STRONGER hypothesis than T-L4's "continuous only") AND requires **`[IsDomain R]`**.
  - `isIntegral_of_forall_continuous_valuation_le_one` (Presheaf:1639): the correct
    continuous-valuations form (Wedhorn 7.18 proper) — but it **(a) requires `[IsDomain R]`** and
    **(b) has a live sub-`sorry`** (the continuity construction = Wedhorn Lemma 7.22, "substantial
    additional infrastructure", per its own docstring).
- **[2] Setting attack (`[IsDomain]` vs case-(b)).** `presheafValue D' = Â⟨T/s⟩` in case-(b)
  (general strongly noetherian) is **NOT a domain**. So BOTH in-repo 7.18 lemmas are inapplicable to
  the actual target. The general non-domain 7.18(1) bottoms at **[Hu2] Lemma 3.3** — and **[Hu2]
  (Huber, *Continuous valuations*, 1993) is NOT in hand** (we have [Hu1] Habilitation + [Hu3] 1994;
  huber1.txt grep found §1.3 Spv theory, not the σ/τ membership bijection).
- **[3] Cross-check with the existing LL chain.** Consistent: `project_faithful_ll_assembly` records
  the faithful (LL) assembly already rests on "2 honest leaves (7.51(2)/7.49 + **[Hu2] 3.3**)". So
  T-L4 = that pre-existing **parked [Hu2] 3.3 external leaf**.
- **What the reviewer got right:** the **ℂ_p red flag is genuinely withdrawn** — leaf #4 is NOT the
  noetherian *density* converse 7.18(3); it is the hypothesis-free-*in-principle* bijection 7.18(1).
  The citation correction is real and valuable.
- **What the reviewer got wrong (formalization reality):** 7.18(1) is **not** a trivial in-repo
  wrapper. It is a genuine **cited external leaf at [Hu2] 3.3 (i)/(ii)** — faithful and acceptable
  per CLAUDE.md, but NOT newly dischargeable. The "delete leaf #4 / short wrapper" instruction does
  not survive contact with the code (non-domain + [IsDomain]-gated in-repo proof + 7.22 sorry +
  [Hu2] not in hand).
- **DECISION POINT for the user (recorded, not auto-resolved):**
  - **(a)** Keep T-L4 PARKED as the cited [Hu2] 3.3 external leaf (faithful; consistent with the LL
    chain already resting on it). Lowest cost; the red flag is gone. **Recommended.**
  - **(b)** Attempt the general non-domain 7.18(1) in-repo: drop `[IsDomain]` from
    `isIntegral_of_forall_continuous_valuation_le_one` (re-do via Spv/supports not FractionRing) AND
    discharge its 7.22 continuity sorry. Substantial (Wedhorn 7.22 = "substantial infrastructure");
    a multi-leaf sub-project, not a wrapper.
  - **(c)** Source [Hu2] (Huber 1993) and cite 3.3 directly (still external; doesn't reduce Lean work).

### Net for the board
- T-L1, T-L2, T-L3 stand (with the itemised real work above; T-L3 is more tractable).
- **T-L4's status changes from "trivial wrapper" → "cited external leaf [Hu2] 3.3, parked"** — the
  red flag is withdrawn but it is NOT a discharge. Update the T-L4 ticket framing accordingly and
  surface the decision to the user.

---

## ★ REVISED per /expert-review (2026-06-19) — read this first

The reviewer (adic-spaces expert) checked the 4-leaf plan against the source. Net effect:
**one leaf's red flag is eliminated, one leaf is greatly simplified, two are confirmed.**
Reply: `.mathlib-quality/expert-review/2026-06-19/reply.md`. Source-verified by us.

- **Leaf #4 — RED FLAG WITHDRAWN.** The correct source is **Wedhorn 7.52(1) = 7.18(1)**
  ("`f ∈ A⁺ ⟺ v(f) ≤ 1 ∀v ∈ Spa(A,A⁺)`", `wedhorn.txt:3619` / `:3161`), which is **stated
  for any affinoid ring — no completeness, Tate, or noetherian ring of definition.** Our
  earlier ℂ_p concern came from conflating it with the *density* converse 7.18(3) (the only
  part needing a noetherian ring of definition). New target: prove 7.52(1) (the τ∘σ=id
  direction, hypothesis-free, content in [Hu1] §3 / [Hu2] 3.3 parts i–ii — NOT iii) and
  wrap the leaf as `v(x)≤1 ∀v∈Spa ⟹ x∈A⁺ ⟹ x∈A°` (the second ⟹ is our already-built
  `IsRingOfIntegralElements.subset_powerBounded`). NUANCE vs reviewer: 7.52(1) is *not* yet
  an in-project lemma (only 7.52(2) `wedhorn_7_52_2_isUnit_iff_forall_not_vle_zero` is), so
  it is a small **hypothesis-free** sub-leaf, not a pure deletion.
- **Leaf #1 — SIMPLIFIED (no Prop 6.18).** Corestrict `ρ : R=𝒪_X(U) → P=∏𝒪_X(Uᵢ)` to the
  closed equalizer `E` of the overlap maps; separation+gluing give a continuous bijection
  `ρ̃ : R → E`; `E` is closed (kernel of the overlap difference map) hence complete +
  countably-based; apply the **already-landed Theorem 6.16** (`BanachOMT.lean`: complete
  target + surjective ⟹ open) to `ρ̃`; continuous+injective+open ⟹ homeomorphism; compose
  with `E ↪ P`. Prop 6.18 (the "Proof. Missing" functional analysis) is **not needed**.
  RISK: do not apply 6.16 to `ρ` into the full `P` (not surjective) — corestrict to `E` first.
- **Leaf #2 — CONFIRMED; openness is automatic.** `A⁺` open ⟹ `Iⁿ ⊆ A⁺` ⟹ `IⁿA₀[T/s]` is an
  open nbhd of 0 in the loc topology, `⊆ A⁺[T/s]`, so `A⁺[T/s]` open ⟹ its integral closure
  `G` open ⟹ `G` is a ring of integral elements of `A[1/s]` (+ 7.19/7.20 for `G ⊆ (A[1/s])°`)
  ⟹ `closure(G)` a ring of integral elements of the completion by **7.47(4)**. RISK: the
  localized plus-ring must contain the generators `T/s` and be integrally closed (it does:
  our def is `closure(image of IntCl(locPlusSubring))`).
- **Leaf #3 — CONFIRMED; only the general (non-noetherian) branch of 7.45 is needed.** Add a
  one-line maximality lemma (for maximal `p`, `p ⊆ supp x` + supp prime ⟹ `supp x = p`).
  Prop 7.41 is the height-1-bound-on-A° step. ℂ_p-safe.
- **Gluing dependency correction (Q4b).** Gluing needs neither leaf #1 nor the former leaf
  #4, but it DOES depend on leaf #2 (relative use over `𝒪_X(U)`) and **leaf #3** (Lemma 7.54
  uses Cor 7.53, whose proof uses maximal-ideal Spa points from Prop 7.51). Record leaf #3
  as upstream of gluing — not "gluing is wholly independent."

**Revised residual: 3 leaves** — #1 (equalizer+6.16 assembly, tractable), #2 (7.47(4)
completion + openness chain), #3 (general 7.45 + maximality). Former #4 → small
hypothesis-free 7.52(1) sub-leaf (possibly mergeable with the leaf #3 / Cont(A) work, since
both are [Hu1] §3 valuation theory). The original per-leaf analysis below is retained for
record; the **revised** statements above supersede it where they differ.

---

## Skeleton location (existing — these are the live sorries, not new decls)
- Leaf #1: `StructureSheaf.lean:1384` `productRestrictionSub_isInducing_tate := sorry`
- Leaf #2: `Presheaf.lean:505-507` `presheafValuePlus_isRingOfIntegralElements` 3 sorry fields
- Leaf #3: `Presheaf.lean:2785` `exists_cont_supp_ge_powerBounded_of_nonOpen_prime := sorry`
- Leaf #4: `FaithfulLocLift.lean:92` `isPowerBounded_of_forall_vle_one_spa_of_complete := sorry`

---

## Leaf #1 — topological inducing of `productRestrictionSub` (Wedhorn Prop 6.18)

### Source situation — RED FLAG (rule 4): Wedhorn does NOT prove this
`wedhorn.txt:2596-2621`: Thm 6.16 (Banach for Tate rings), Prop 6.17 (noeth ⟺ ideals
closed), Prop 6.18 (f.g. modules: unique complete topology + continuity/openness) — **all
three say literally "Proof. Missing"**. Wedhorn defers the entire Banach/noetherian-Tate
functional analysis to the primary literature. So the faithful route transcribes **[Hu1]**
(§3.5 "Tate-Ringe mit noetherschem Definitionsring", `huber1.txt:146`) and/or **BGR**
(classical Banach for affinoid algebras), NOT Wedhorn.

### Verbatim (Wedhorn `wedhorn.txt:2615-2621`)
> "Proposition 6.18. Let A be a complete noetherian Tate ring. (1) Every finitely
> generated A-module has a unique A-module topology that is complete and that has a
> countable fundamental system of open neighborhoods of 0. (2) Let f : M → N be an
> A-linear map of finitely generated modules ... Then f is continuous and the map
> f : M → f(M) is open. Proof. Missing"

### Decomposition (must mirror [Hu1]/BGR, not invent)
- **L1.1 — Thm 6.16 (Banach OMT, units→0 form).** Status: *already landed sorry-free* in
  the project (`wedhorn_6_16_of_topNilpUnit`, per the faithful-OMT work). Source for the
  units→0 strengthening: Henkel 2014 (`Henkel-...pdf`). VERIFY this claim against the code.
- **L1.2 — Prop 6.17 (noeth ⟺ every submodule closed).** Source: [Hu1] §3.5 / BGR.
- **L1.3 — Prop 6.18(1) (unique complete f.g.-module topology).** Source: [Hu1] §3.5.
  Wedhorn Remark 6.19 (`wedhorn.txt:2622`) gives the explicit basis `{sⁿM₀}`.
- **L1.4 — Prop 6.18(2) ⟹ `productRestrictionSub` inducing.** The Lean leaf is the
  inducing of `productRestrictionSub A C : O_X(C.base) → ∏ O_X(Dᵢ)`; 6.18(2) gives that an
  A-linear map of f.g. modules is continuous + open-onto-image. NEEDS: identify `O_X(C.base)`
  and the product as f.g. modules + apply 6.18(2). **This is the genuine in-project assembly.**

### Adversarial attacks
- **[A4 source-drift / A-structure]** 6.18 requires **complete *noetherian* Tate**. Our
  headline has `[IsStronglyNoetherian A]` + `[IsNoetherianRing A]` + complete Tate — OK at
  base. But `productRestrictionSub` lives over completions; need 6.18's hypotheses to hold
  for the completed structure rings (they're strongly-noeth Tate, established). CHECK.
- **[A5 discharge]** Is `wedhorn_6_16_of_topNilpUnit` genuinely sorry-free and does its type
  match what 6.18(2)→inducing needs? Must `lean_verify` / `#print axioms`.
- **[A1 deepest-leaf]** The "Proof Missing" is the tell: 6.18(2)→inducing is real
  functional analysis. Risk that the in-repo assembly needs the f.g.-module-topology
  uniqueness (6.18(1)), which is itself unproved. **This is the deepest leaf.**
- Verdict: **NOT a clean leaf** — it is an internal node whose sub-leaves (6.16✓, 6.17, 6.18(1),
  6.18(2)→inducing) need their own decomposition from [Hu1] §3.5 / BGR. Ticket as a sub-tree.

---

## Leaf #2 — `(presheafValue D)⁺ = Ĉ` is a ring of integral elements (Wedhorn 7.47(4))

### Source situation — proof IS available ([Hu1] 2.4.3, German, concrete)
Wedhorn 7.47(4) (`wedhorn.txt:3557`) "Rings of integral elements of A ↔ of Â. Proof.
[Hu1] 2.4.3." The proof is `huber1.txt:7465-7560` (German, §2.4.3).

### Verbatim ([Hu1] `huber1.txt:7491-7512`, German, lightly de-OCR'd)
> "iv) die Ganzheitsringe von A und die Ganzheitsringe von Â [correspond].
> Beweis: ... Ist H ein in Â ganz abgeschlossener Unterring von Â, so ist natürlich
> i⁻¹(H) ganz abgeschlossen in A. Zu zeigen bleibt noch: Ist G ein in A ganz
> abgeschlossener und offener Unterring von A, so ist Ĝ ganz abgeschlossen in Â.
> Sei a ein Element von Â, das ganz über Ĝ ist. Wir zeigen a ∈ Ĝ = î(G). Dazu ist zu
> zeigen, daß U ∩ î(G) ≠ ∅ für jede Umgebung U von a in Â. ..."

### Decomposition (mirrors [Hu1] 2.4.3's structure)
- **L2.1 — bounded/top-nilpotent transfer:** `i⁻¹(Â°)=A°` ([Hu1] 7492-7495). This is the
  Lean `subset_powerBounded` field route (Ĉ ⊆ Â° via Â° = closure-stable). Needs:
  continuous-hom preserves power-bounded (`IsPowerBounded.map`, exists `Presheaf.lean:3612`)
  + Â° clopen (`isOpen_powerBoundedSubring` `HuberRings.lean:257` → open subgroup closed).
- **L2.2 — easy half:** H integrally closed in Â ⟹ i⁻¹(H) integrally closed in A (7505).
  (Not directly the Lean field, but the bijection's other direction.)
- **L2.3 — hard half (`isIntegrallyClosed` field):** G integrally-closed + **open** in A ⟹
  Ĝ = closure(G) integrally closed in Â (`huber1.txt:7510-7560`). The density argument:
  a integral over Ĝ ⟹ show every nbhd U of a meets î(G), via H = integral closure of G in
  A (open since G open) and the monic relation `i(b)ⁿ + cₙ₋₁i(b)ⁿ⁻¹ + … = 0`.
- **L2.4 — `isOpen` field:** Ĝ open (closure of an open subgroup is open).

### Adversarial attacks
- **[A4 source-drift — IMPORTANT]** Our Lean def is `completedPlusSubring D :=
  closure(image of IntCl(locPlusSubring))` — i.e. Ĝ with **G = IntCl(locPlusSubring)**, the
  *precompletion* ring of integral elements of `A_s`. [Hu1] 2.4.3(iv) requires G to be a
  ring of integral elements of `A_s` (= integrally closed + open + ⊆ A_s°). So leaf #2
  **transitively requires the precompletion fact** (Wedhorn 7.19/7.20: `(A⁺[T/s])^int` is a
  ring of integral elements of `A_s`) as a SEPARATE sub-leaf. Is `IntCl(locPlusSubring)`
  open in `A_s`? (needs `locPlusSubring` open ⟹ IntCl open). **Flag: add precompletion
  sub-leaf; verify "open" holds.**
- **[A3 hidden hyp]** [Hu1] 2.4.3 needs **G open** (used to make H open). Our G =
  IntCl(locPlusSubring): is it open? Only if locPlusSubring open in A_s. CHECK — possible
  gap.
- **[A5 discharge]** `IsPowerBounded.map` + `isOpen_powerBoundedSubring` exist (verified by
  grep); the density argument (L2.3) is new infra (~the Huber proof, faithful).
- Verdict: **internal node**, 4 sub-leaves; faithful (proof available in [Hu1]); but the
  precompletion 7.19/7.20 + the "open" check are real sub-obligations.

---

## Leaf #3 — analytic Spa-point of a non-open prime (Wedhorn 7.45 + 7.41)

### Source situation — Wedhorn-INTERNAL (fully proved; the most tractable leaf)
Full proof at `wedhorn.txt:3438-3535`. NOT deferred to Huber.

### Verbatim (Wedhorn `wedhorn.txt:3438-3444`, Prop 7.41)
> "Proposition 7.41. Let A be an f-adic ring and let x ∈ Cont(A)ᵃ be of height 1. Then
> x(a) ≤ 1 for all a ∈ A°. ... Proof. Let a ∈ A° and assume that x(a) > 1. Choose b ∈ A°°
> with x(b) ≠ 0 ... As Γx has height 1, it is archimedean (Proposition 1.14). Hence there
> exists n ∈ N with x(aⁿ) > x(b)⁻¹, i.e., x(aⁿb) > 1. But as a is power-bounded, aⁿb ∈ A°°
> and thus the continuity of x implies x(aⁿb) < 1. Contradiction."

### Decomposition (mirrors Wedhorn 7.45's proof chain)
- **L3.1 — Prop 7.41** (height-1 ⟹ x(a)≤1 on A°). `wedhorn.txt:3438`, 4-line proof.
  Needs: `Γx` archimedean from height 1 (Prop 1.14 analogue), A°°-continuity, A°° def.
  PROVABLE.
- **L3.2 — Lemma 7.44(3)** (`wedhorn.txt:3469`): for B open ⊆ A, `Cont(A)ᵃ ≅ Cont(B)ᵃ`
  preserving Γ. PROVABLE (the Bₛ→Aₛ iso for non-open primes).
- **L3.3 — Remark 7.42(2)/4.12** (`wedhorn.txt:3450`): analytic ⟹ microbial ⟹ ∃ height-1
  vertical generization. The `restrictToConvex`-to-height-1 step.
- **L3.4 — the 7.1.2 retraction `r : Spv(B₀) → Spv(B₀,I)`** + **Theorem 7.10** (Cont
  characterization). In-repo this is `restrictToConvex` — **already present but with a
  sorry**. This is leaf #3's deepest dependency.
- **Assembly — Lemma 7.45 general case** (`wedhorn.txt:3491-3506`): u dominating m ⊇ p₀ →
  r(u) ∈ Cont(B₀) non-analytic (Thm 7.10, Lemma 7.5(3)) → v analytic on A (7.44(3)) →
  x height-1 (4.12) → x ∈ Spa (7.41).

### Adversarial attacks
- **[A3 hidden hyp — GOOD NEWS]** Wedhorn 7.45's *general case* needs only "complete
  affinoid" — NO noetherian ring of definition. (The noeth-ring-of-def is only for the
  *additional* "discrete valuation, supp x = p" refinement, which the leaf does NOT need.)
  So leaf #3 is ℂ_p-safe. ✓
- **[A5 discharge]** Deepest dependency = `restrictToConvex` (7.1.2 retraction), in-repo
  with a sorry; + Theorem 7.10. CHECK their status — leaf #3 reduces to those.
- **[A1]** Prop 1.14 (height-1 ⟹ archimedean value group) — is it in repo/mathlib? CHECK.
- Verdict: **internal node, Wedhorn-faithful, most tractable**; bottoms at the in-repo
  `restrictToConvex` sorry + Thm 7.10 + Prop 1.14. Strong ticket candidate.

---

## Leaf #4 — power-bounded from Spa-bound (`isPowerBounded_of_forall_vle_one_spa`)

### Source situation + ADVERSARIAL RED FLAG
The Lean leaf: `∀v∈Spa, v(x)≤1 ⟹ x ∈ A°` (power-bounded). Cited to [Hu2] 3.3. Wedhorn's
σ(A⁺) remark (`wedhorn.txt:3168-3174`, "Proof. [Hu2] Lemma 3.3"):
> "(2) Let A⁺ ... be a ring of integral elements. Then every point of Cont(A) is a vertical
> specialization of a point in σ(A⁺); ... σ(A⁺) is dense in Cont A.
> **(3) If A is a Tate ring and has a noetherian ring of definition, then also the converse
> of (2) does hold:** if A′ ∈ RA such that σ(A′) is dense in Cont A then A′ ⊆ A°."

**The leaf is the CONVERSE direction (something-bounded-on-Spa ⟹ power-bounded), which
Wedhorn's part (3) supplies ONLY under "Tate + noetherian ring of definition"** — the
ℂ_p-FALSE noeth-ring-of-definition hypothesis (the exact defect this project has been
purging). Run the ℂ_p test: ℂ_p is complete Tate, NO noetherian ring of definition, and
the leaf's statement (v≤1 on Spa ⟹ power-bounded) — does it hold for ℂ_p? If part (3) is
the only route and it needs noeth-ring-of-def, the leaf may be **false-as-stated for ℂ_p**,
or need a different (pair-free) route.

### Decomposition — DEFERRED pending the ℂ_p verdict
Do NOT decompose until the adversarial flag is resolved:
1. Re-read [Hu2] 3.3 (content in [Hu1] §3, `huber1.txt` Cont(A)) — is the converse really
   noeth-ring-of-def-only, or is there a complete-affinoid route (à la 7.45)?
2. Re-examine the Lean leaf's USE site (FaithfulLocLift flatness): does the flatness chain
   genuinely need the full converse, or only `x ∈ A⁺ ⟹ v(x)≤1` (the EASY direction)?
3. If the leaf as stated needs noeth-ring-of-def → B2 candidate (restate or re-route).

### Adversarial attacks
- **[A2 ℂ_p edge case]** ℂ_p: complete Tate, no noeth ring of def. Leaf must hold here
  (8.28(b) holds for ℂ_p). If the only proof needs noeth-ring-of-def → leaf false-for-ℂ_p.
- **[A4 source-drift]** Does the Lean statement match the EASY direction (7.41-style, A° via
  Spa-bound) or the HARD converse (3.3(3), noeth-only)? CRITICAL to pin.
- Verdict: **REVIEW-PENDING / B2-candidate** — strongest `/expert-review` question.

---

## Feasibility assessment (first pass)

The decomposition is **source-grounded and feasible to plan**, with these honest findings:
- **Leaf #3** (analytic Spa-point) is the most tractable: Wedhorn-internal, ℂ_p-safe, bottoms
  at the in-repo `restrictToConvex` sorry + Thm 7.10 + Prop 1.14.
- **Leaf #2** (ring-of-integral-elements completion) has a concrete [Hu1] 2.4.3 proof;
  decomposes into 4 sub-leaves + a precompletion (7.19/7.20) obligation; the "G open" check
  is a possible gap.
- **Leaf #1** (6.18 inducing) is the deepest: Wedhorn says "Proof Missing"; the real proof
  is [Hu1] §3.5 + BGR functional analysis (6.16 landed; 6.17 + 6.18(1)/(2)→inducing remain).
- **Leaf #4** is a genuine ADVERSARIAL CATCH: its cited source ([Hu2] 3.3 converse) needs
  "noetherian ring of definition", the ℂ_p-false hypothesis — must resolve (ℂ_p test +
  use-site analysis + `/expert-review`) before it can be ticketed; possible B2.

**Recommended order:** #3 (tractable, Wedhorn-faithful) → #2 (concrete [Hu1] proof) → #1
(deep, [Hu1]§3.5/BGR) ; #4 to `/expert-review` first (ℂ_p red flag).

**NOT done (this is decompose-pass-1):** the full 5-attack-per-sub-leaf treatment, the Lean
skeleton refinement, and the per-leaf provability `lean_verify`s — to be completed per leaf
before ticketing, and after `/expert-review` settles leaf #4.

---

# T-L4 — Huber [Hu2] Lemma 3.3(i): `isPowerBounded_of_forall_vle_one_spa_of_complete`

*(decompose pass 2026-06-21, un-park; sources read verbatim: huber2.txt:585-617 (Thm 3.1) +
:624-658 (Lemma 3.3). All deep discharges `lean_verify`'d present — see Step-4 block.)*

## Goal (Lean, canonical)
`isPowerBounded_of_forall_vle_one_spa_of_complete` (FaithfulLocLift.lean:97): for `B := presheafValue D'`,
`(∀ w ∈ Spa B B⁺, w.vle x 1) → IsPowerBounded x`.

## Step 1 — prose proof (transcribed from Huber, A := B = presheafValue D', G := B⁺)
Spa(B,B⁺) = σ(B⁺) = {v ∈ Cont B | v(b)≤1 ∀b∈B⁺}. The hypothesis says x ∈ τ(σ(B⁺)) :=
{a | v(a)≤1 ∀v∈σ(B⁺)}. By Huber 3.3(i), τ(σ(G))=G for every open integrally-closed G, so x ∈ B⁺;
and B⁺ ⊆ B° (Def 7.14), so x is power-bounded. The substantive content is **τ(σ(G)) ⊆ G**, by
contradiction: if a ∈ τ(σ(G))\G, build v ∈ σ(G) with v(a)>1, contradicting a ∈ τ(σ(G)).

## Step 2/2.5 — sub-lemmas (mirror Huber's proof; Lean skeleton = first /beastmode step)

- **HU-a** `not_isUnit_inv_of_not_mem` (leaf, integral-closure)
  - Source (huber2.txt:635-637, verbatim):
    > "The element a⁻¹∈G[a⁻¹] is not a unit of G[a⁻¹] (since otherwise a∈G[a⁻¹] which implies that
    > a is integral over G and hence a∈G)."
  - Lean↔source: `a ∉ G → ¬ IsUnit (⟨a⁻¹⟩ : G[a⁻¹])`. G=B⁺ integrally closed in B (ROIE).
  - Discharge: `IsIntegral` + integral-closure of `B⁺`. mathlib `isIntegral_of_…`; ROIE closedness.

- **HU-b** `exists_minimalPrimes_le_containing_inv` (leaf, mathlib)
  - Source (637-639): > "there exists a prime ideal p of G[a⁻¹] with a⁻¹∈p. Let q be a minimal
    prime ideal of G[a⁻¹] with q⊆p."
  - Discharge: `Ideal.exists_le_maximal` (a⁻¹ non-unit ⟹ in a maximal p) + `Ideal.exists_minimalPrimes_le`.

- **HU-c** `exists_dominating_valuation` (leaf, ⭐MATHLIB CRUX — verified)
  - Source (639-641): > "Choosing a valuation ring of qf(G[a⁻¹]/q) which dominates the local ring
    (G[a⁻¹]/q)_{p/q} we obtain a valuation s of G[a⁻¹] with q=supp(s), s(g)≤1 for all g∈G, and
    s(x)≤1 for all x∈p, in particular s(a⁻¹)≤1."
  - Discharge (verified): `IsLocalRing.exists_factor_valuationRing` (Mathlib.RingTheory.Valuation.
    LocalSubring) — `(f : R →+* K)→∃ A, (∀x, f x∈A) ∧ IsLocalHom (f.codRestrict …)`, at
    `R=(G[a⁻¹]/q)_{p/q}`, `K=Frac(G[a⁻¹]/q)`. Local-hom ⟹ s≤1 on the ring, <1 (into 𝔪) on p/q.

- **HU-d** `exists_lifted_spv_valuation` (leaf, valuation-lift bookkeeping — hardest)
  - Source (641-655, incl. the (c) argument):
    > "Since there exists a prime ideal of A_a lying over q, there exists a valuation t of A_a lying
    > over s. Put u=t|A∈Spv A and v=u|cΓ∈Spv A. Then (a) v(a)>1 (b) v(g)≤1 ∀g∈G (c) v(x)≤1 ∀x∈A°°
    > (d) v∈Spv(A,A°°A). … Let x∈A°°. Since G is open, ∃ n∈ℕ with xⁿa∈G. … x∈G (G open and integrally
    > closed). Hence in G[a⁻¹] we have xⁿ=g·a⁻¹ with some g∈G. Since a⁻¹∈p, xⁿ∈p, hence s(xⁿ)≤1 which
    > implies v(x)≤1."
  - Discharge: mathlib `Valuation.comap` (restriction along `B→B_a`, `A→A_a`) + valuation extension
    along `G[a⁻¹]→B_a` (`Valuation` on `Frac`); project `Spv`/`vle` API. May sub-split (a)/(b)/(c)/(d).

- **HU-e** `mem_spa_of_lifted` + contradiction (composition)
  - Source (656-658): > "We conclude from (3.1) and (c),(d) that v is a continuous valuation, and
    with (b) we obtain v∈σ(G). Now (a) implies a∉τ(σ(G)) which is a contradiction."
  - (3.1) = Huber Thm 3.1 (585-588, verbatim): > "Cont A = {v∈Spv(A,A°°A) | v(a)≤1 for every a∈A°°}."
    = Wedhorn 7.10 reverse.
  - Discharge (verified): project `Spv.isContinuous_of_isInSpvAI_of_lt_one` (SpvAI.lean:294,
    **lean_verify'd axiom-clean** [propext, Classical.choice, Quot.sound]) gives continuity from
    (c)+(d); compose with (b) for v∈Spa; (a) contradicts the hypothesis.

- **L-714** (leaf, project, ALREADY available): `B⁺ ⊆ B°` = `IsRingOfIntegralElements.subset_powerBounded`
  (used Cor832:1626). Closes `x∈B⁺ ⟹ IsPowerBounded x`.

## Step 4 — provability check (all leaves discharged from existing infra)
| leaf | discharge | status |
|------|-----------|--------|
| HU-a | integral-closure of B⁺ (ROIE) + `IsIntegral` | project+mathlib |
| HU-b | `Ideal.exists_le_maximal`, `Ideal.exists_minimalPrimes_le` | mathlib |
| HU-c | `IsLocalRing.exists_factor_valuationRing` | mathlib ✓verified-exists |
| HU-d | `Valuation.comap` + extension; project Spv API | mathlib+project |
| HU-e | `Spv.isContinuous_of_isInSpvAI_of_lt_one` | project ✓lean_verify'd-axiom-clean |
| L-714 | `IsRingOfIntegralElements.subset_powerBounded` | project ✓in-use |

## Step 4.5 — adversarial (key leaves)
- HU-a Attack (hyp-strength): does it need `G` integrally closed? YES — a⁻¹ unit ⟹ a integral over G;
  conclusion `a∈G` needs G=its own integral closure in B. B⁺ IS integrally closed (ROIE def). No drift.
- HU-c Attack (discharge): `IsLocalRing.exists_factor_valuationRing` requires the SOURCE a local ring
  + a map to a FIELD. We have `(G[a⁻¹]/q)_{p/q}` local (localization at p/q) and `Frac(G[a⁻¹]/q)` a field
  (q minimal ⟹ G[a⁻¹]/q a domain). Both hold. ✓
- HU-e Attack (source-drift on 3.1): is `Spv.isContinuous_of_isInSpvAI_of_lt_one` the SAME criterion
  as Huber 3.1? Huber: v∈Spv(A,A°°A) ∧ v(a)≤1 ∀a∈A°° ⟹ continuous. Project lemma name + the SpvAI
  docstrings ("Wedhorn 7.10 reverse, cofinality disjunct") match. ✓ (verify exact hyp shape at ticket time).
- Whole-composition Attack (could HU-a..e be true and τ(σ(G))⊆G false?): no — the contradiction is
  Huber's; HU-d (d) `v∈Spv(B,B°°B)` + (c) feed HU-e's continuity criterion EXACTLY; (a)+(b) give the
  σ(G)-membership-with-v(a)>1 contradiction. Composition faithful to huber2.txt:656-658.

## Feasibility verdict
**FEASIBLE in-repo.** The two pieces that made this look "external/deep" — the dominating valuation
(HU-c) and the continuity criterion (HU-e) — are BOTH discharged (mathlib crux + axiom-clean project
7.10-reverse). Remaining work is connective tissue (HU-a integral-closure, HU-b minimal prime, HU-d
valuation-lift bookkeeping) in the project's Spv encoding; HU-d is the bookkeeping-heavy leaf. No
published-paper-scale gap. First /beastmode step: state HU-a…e `:= by sorry`, `lake build`, then fill
HU-c + HU-e (verified discharges) before HU-d.
