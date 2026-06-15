# Review brief — Tate Acyclicity (Round 4 / Session 26)

*Prepared 2026-05-18 for the same external mathematician who replied to round 3 (the Path α decision was based on your reply). Self-contained for re-reading, with deltas from round 3 explicitly called out. Round-4 trigger: an adversarial pre-flight pass across all 56 in-scope leaves on the IsSheafy / Tate-acyclicity chain, looking for blockages before a long marathon execution session.*

---

## 1. Goal (unchanged from round 3)

We are formalising the structure presheaf $\mathcal{O}_X$ on $X = \mathrm{Spa}(A, A^{+})$ and proving Wedhorn Theorem 8.28(b): for $A$ a **strongly noetherian Tate** affinoid ring, $\mathcal{O}_X$ is a sheaf of complete topological rings. The IsSheafy predicate carries the conjunction of (i) the equaliser property over each rational covering and (ii) compatible completion topology. Notation throughout is Wedhorn's: $A^{\circ}$ for power-bounded, $A^{\circ\circ}$ for topologically nilpotent, $A^{+}$ for the chosen ring of integral elements, a *pair of definition* $P = (A_0, I)$ with $A_0$ a ring of definition and $I$ an open finitely generated ideal of definition.

## 2. What round 3 settled (executive recap)

Round 3 locked **Path α**: every Wedhorn-clean theorem on the IsSheafy chain takes a *parametric* pair of definition together with a noetherianness hypothesis on its ring of definition,

$$(P : \mathrm{PairOfDefinition}\,A) \quad [\mathrm{IsNoetherianRing}\ P.A_0],$$

as explicit arguments. This is your "rephrase as Wedhorn 8.28(a) Case (a), don't try to derive noeth-$A_0$ from strong noetherianity" verdict. The deleted B2/B3/B4 chain (the false Wedhorn 6.18 forward direction in the project's setting) stays deleted.

Round 3 also gave verdicts on five questions; in particular:
- Q-S24.1: yes, Example 6.38 preserves noeth ring of definition from noeth $A_0$ — this motivated introducing the lemma `presheafValue_pairOfDefinition_isNoetherian` as the single highest-leverage unblocker on the propagation side.
- Q-S24.4: yes, add $[\mathrm{CompleteSpace}\ A]$ + uniformity bundle to the headline theorem, since Wedhorn 8.28(b) is implicitly stated for complete affinoid rings.

The headline theorem in its final form is now: under the hypothesis bundle $[\mathrm{IsTateRing}\ A] [\mathrm{IsNoetherianRing}\ A] [\mathrm{IsStronglyNoetherian}\ A] [T_2\,A] [\mathrm{NonarchimedeanRing}\ A] [\mathrm{UniformSpace}\ A] [\mathrm{IsUniformAddGroup}\ A] [\mathrm{CompleteSpace}\ A] [\mathrm{IsDomain}\ A]$, plus the parametric $(P, [\mathrm{IsNoetherianRing}\ P.A_0])$, we have $\mathrm{IsSheafy}\ A$.

(The `[IsDomain A]` hypothesis stays — this is one of the round-4 decisions we report below.)

## 3. Session 26 (round 4) — what's new

Round 4 was an adversarial "find every blocker before /beastmode hits them" pass. We dispatched **six parallel reviewer agents** across nine clusters and asked each: where will a methodical executor get stuck? The output is consolidated in our internal audit document. The substantive findings are organised below.

### 3.1 Cluster L verdict (the good news)

You may recall that the Wedhorn 8.31 wrappers in the project (Lemma 8.31(1) faithful flatness of $A\langle X \rangle / A$ and Lemma 8.31(2) flatness of the quotients by $(f - X)$ and $(1 - fX)$) had been hard-deleted because their bodies routed through the false B2/B4 chain. We were not sure whether parametric replacements existed.

The audit confirms: **the substantive theorems exist and are PROVED, with the Path α parametric signature**.

| Wedhorn 8.31 facet | Project home | Signature |
|---|---|---|
| 8.31(1) | `TateAlgebra.faithfullyFlat_general` | $(P) [\mathrm{IsNoetherianRing}\ P.A_0] : \mathrm{Flat}\ A\,A\langle X \rangle$ + faithful flatness |
| 8.31(2)$^-$ | `TateAlgebra.flat_quotient_fSubX_general` | $(P) [\mathrm{IsNoetherianRing}\ P.A_0]\,(f : A) : \mathrm{Flat}\ A\,(A\langle X \rangle / (f - X))$ |
| 8.31(2)$^+$ | `TateAlgebra.flat_quotient_oneSubfX_general` | $(P) [\mathrm{IsNoetherianRing}\ P.A_0]\,(f : A) : \mathrm{Flat}\ A\,(A\langle X \rangle / (1 - fX))$ |

All three are **axiom-clean** (only `propext`, `Quot.sound`, `Classical.choice`). The proofs route through `TateAlgebra.faithfullyFlat_general` → an abstract `Module.Flat.quotient_of_flat_of_saturated` engine + regularity + saturation. Live consumers already in the chain: `presheafValue_flat_of_tateQuotient`, `presheafValue_flat_of_canonical`, `RestrictionFlatness`-tagged transport.

Recommendation: do **not** re-introduce the deleted AuditPass1 wrappers. They were a corrupted re-statement of the substance; the substance lives at the correct signature.

### 3.2 The five concrete Path α discharge breaks

These were surfaced by tracing the dependency graph downward from the headline theorem. Each one is a literal `sorry` in the current code or an unfixable-on-the-current-route situation; each must be resolved before /beastmode can close `IsSheafy`.

**(B-1) The headline theorem itself is a literal sorry with no delegation written.** The proof body is just `sorry`. The intended discharge per the docstring is "delegate to A1" (the variant that takes an explicit $(P, [\mathrm{IsNoetherianRing}\ P.A_0])$) but no `exact` is written.

**(B-2) A1's embedding side is a literal sorry.** A1 says: under the same hypotheses, IsSheafy holds. The proof body splits into the equaliser-condition's two halves (embedding via the product restriction, plus gluing) and the embedding half is sorried, pending the "Lane C IsInducing for an arbitrary rational covering" lemma (`productRestrictionSub_isInducing_tate`), which in turn needs the Wedhorn 8.34 refinement-tree existence (the F-cluster's headline result).

**(B-3) A2 inherits two literal sorries.** A2 takes the embedding and gluing as parameters, so does NOT have an inherent block — but its callers route through `rationalCovering_hasSeparation` (uses `tateAcyclicity` Part 1) and `rationalCovering_hasGluing` (uses `tateAcyclicity` Part 2), both of which are literal sorries in `LaurentRefinement.lean`. The reason those are sorries is the import cycle described in 3.3 below.

**(B-4) The audit-pass-2 wrapper `cor_8_32_clean_proof` is structurally incompatible with its target.** Its body delegates to a "product faithful flatness of restrictions" theorem that requires (i) the deleted wrong-shaped global Spa-points lemma B5 and (ii) the sorried `hSpa_surj_from_spanTop`. Both are downstream of the deleted false `restrictionMap_isLocalization` (Wedhorn Prop 8.15 IsLocalization-style misframe). **There is no fix on this route**: the route assumes a fact (rational restriction = `IsLocalization.Away`) that is FALSE in general (convergent-denominator tails, recorded earlier).

**(B-5) The proposed "II.2 wrapper" `tateAcyclicity_part2_gluing_via_flat_descent` is degenerate.** Its body simply calls `rationalCovering_hasGluing`, which calls back `tateAcyclicity` Part 2 (the sorry). So this wrapper has not moved the sorry — it has relabeled its location. The composer `isSheafyComplete` lists it as a "discharged leaf II.2" in its dependency graph, but it isn't.

In addition, we surfaced a silent blocker: the $\mathrm{HasLocLiftPowerBounded}\,A$ instance (`B1` in the cluster taxonomy) is itself sorried, and is required by every $\mathrm{presheafValue}$-using statement in the post-section namespace where the headline theorem lives. Without it, the headline theorem's body fails to elaborate even before any maths is attempted.

### 3.3 Three architectural decisions about to execute

The user has decided three things based on the audit:

**(D-1) `[IsDomain A]` stays on the headline theorem.** The earlier Session-24 plan to drop it was based on a docstring promise that didn't survive the audit: the discharge route through `rationalCovering_hasSeparation`'s empty-cover branch uses `Ideal.isPrime_bot`, which requires `IsDomain`. Removing it would force refactoring the empty-cover branches for no mathematical gain. The headline theorem now matches A1's hypothesis bundle exactly and is, in effect, a re-export of A1 under the parametric Path α signature.

**(D-2) Refactor `tateAcyclicity` Parts 1+2 from `LaurentRefinement.lean` into `TateAcyclicityFinalAssembly.lean`.** This breaks the import cycle in (B-2)/(B-3): `Cor832.lean` (where the clean Wedhorn 8.32 product faithful flatness will live in a new combinator) currently imports `LaurentRefinement.lean`. So the gluing proof, which needs Cor 8.32's faithful flatness, cannot live in `LaurentRefinement.lean`. Moving the two top-level acyclicity statements (plus `rationalCovering_hasSeparation` and `rationalCovering_hasGluing` wrappers) downstream of `Cor832.lean` is a purely structural refactor with no mathematics changed; after the move, the gluing proof gets to use the new `cor_8_32_clean_via_laurent` combinator + the existing Stacks-023N descent equaliser already proved in the project as `faithfullyFlat_descent_equalizer`.

**(D-3) Build the Spa.comap framework in full (the `C3` ticket), not parametrically.** The lemma `Spa_presheafValue_eq_rationalOpen` (Wedhorn 8.2) identifies $\mathrm{Spa}\,(\mathcal{O}_X(D), \mathcal{O}_X(D)^{+})$ with the rational subset $R(T/s) \subset \mathrm{Spa}\,A$ for $D = (T, s)$ a rational locale datum. The project has the underlying pullback map (`Spa.comap_of_continuousRingHom` + continuity) axiom-clean already; what's missing is the image identification (`Spa.comap_image_eq_rationalOpen`) and the inverse. Estimated ~500 LOC. Once built, this unblocks the $\mathrm{HasLocLiftPowerBounded}$ instance (the silent blocker above) and the bridge lemmas that connect the completion-side power-bounded calculations (Wedhorn 7.41) to the rational-subset-level statements.

### 3.4 Seven new B2 candidates (logged this session)

In addition to the architectural breaks, the adversarial pass found seven new statements that are false, under-hypothesised, or otherwise unprovable as currently stated. Each has been recorded with timestamp and concrete counterexample where applicable.

1. **Missing $[\mathrm{CompleteSpace}\ A]$ on Wedhorn 7.51(2)** (the lemma "for $A$ complete affinoid and $\mathfrak{m}$ a maximal ideal, $\exists v \in \mathrm{Spa}\,A$ with $\mathrm{supp}\,v = \mathfrak{m}$"). The project's version drops the completeness hypothesis. Without it, $\mathfrak{m}$ need not be closed (the natural argument routes through `maxIdeal_isClosed_of_complete_huber`, which needs completeness). Fix: add the completeness bundle.

2. **Missing $[\mathrm{IsAdicComplete}\ P.I\ P.A_0]$ on Wedhorn 7.45 intermediate** (the dominating valuation subring lemma). Without adic-completeness of $P.A_0$ in the $I$-adic topology, the step $I + \mathfrak{p}_0 \neq \top$ can fail. Concrete counterexample: $A = \mathbb{Z}[X]$ with $P.A_0 = \mathbb{Z}[X]$, $P.I = (X)$, $\mathfrak{p} = (1 - X)$. Then $1 = X + (1 - X) \in P.I + \mathfrak{p}$, so $I \cdot R' = R'$ and the dominating valuation subring has no nonunit pulled back from the rational direction. Fix: add the adic-completeness instance (the downstream Wedhorn 7.45 statement already has it).

3. **The intersection $\bigcap_n (f)^n = 0$ for $f$ a non-unit fails in non-domain noeth complete Tate.** This is the route the project uses for `laurentCover_exact_general` (Wedhorn 8.33). Counterexample: $A = \mathbb{Q}_p \times \mathbb{Q}_p$ (a product of two noeth complete Tate rings, no longer a domain). Take $f = (p, 0)$. Then $(f)^n = (p^n, 0) \cdot A = \{(p^n a, 0) : a \in \mathbb{Q}_p\}$. By the idempotent $(0, 1) \cdot f = 0$, the intersection contains every $(0, c)$ for $c \in \mathbb{Q}_p$, so it is not $\{0\}$. Fix: either re-add `[IsDomain A]` to the 8.33 statement (matching F4's domain assumption, as per the user's general policy in 3.3) or replace the Krull route with a different Tate-topological injectivity argument.

4. **Wedhorn Cor 7.32 finset form** silently relies on the compactness of $\mathrm{Spa}\,A$. The singleton version (`exists_dominating_unit_noHArch`) takes the compactness as an explicit hypothesis; the finset version drops it; but the natural inductive proof needs it. Either the signature should take it explicitly, or the project needs a no-h-Archimedean `CompactSpace` instance (currently absent).

5. **Wedhorn 8.31 (in disguise as a project sub-lemma)** — `_sub_lemma_L5_1_1_tateAlgebra_eq_adicCompletion` was a vacuous placeholder $\exists e : X \simeq^+_* X,\ e = e$ discharged by reflexivity. This violates the project's explicit "no vacuous-conclusion stand-ins" rule. **Fixed this session**: the statement now honestly asserts $\mathrm{TateAlgebra}\,A \cong (P.A_0 \otimes A) \otimes \widehat{P.A_0[X]}$ (the base change of the adic completion of the one-variable polynomial extension of $P.A_0$). The body is now an honest sorry. See Q8 below for the encoding question.

6. **The headline theorem's docstring contradicts its signature.** The signature still carries `[IsDomain A]`; the docstring promised "without `[IsDomain A]`" (per the Session-24 plan). Per decision (D-1) above, we have kept `[IsDomain A]` and updated the docstring to match — but this surfaced a class of risk that workers reading docstrings could waste cycles trying to remove a hypothesis the proof actually needs.

7. **The proposed II.2 wrapper is degenerate** (already discussed in 3.2 break B-5): the wrapper does not move the sorry, and the dependency graph in the composer `isSheafyComplete` lists it misleadingly as a discharged leaf.

### 3.5 Stacks 0316 sub-development (skeleton landed)

The mathlib gap for "the $I$-adic completion of a noetherian ring is noetherian" (Stacks tag 0316 = Lemma 10.97.6) is being closed as a project-internal sub-development. The skeleton file `AdicCompletionNoetherian.lean` has five sub-leaves and compiles cleanly with sorries only:

- L2: $\mathrm{MvPowerSeries}(\mathrm{Fin}\,n)\,R$ is noetherian when $R$ is. (Mathlib has the single-variable version; the multivariate case is a documented mathlib TODO. We route via the iso $\mathrm{MvPowerSeries}(\mathrm{Fin}(n+1))\,R \cong \mathrm{MvPowerSeries}(\mathrm{Fin}\,n)\,R\,\llbracket X \rrbracket$ plus induction.)
- L3: the evaluation ring map $R \llbracket X_1, \ldots, X_n \rrbracket \to \widehat{R}$, $X_i \mapsto f_i$ for $f_i \in I$, built from the universal property of formal power series plus the Cauchy convergence of partial sums in $\widehat{R}$.
- L4: surjectivity of the evaluation map. This is the workhorse Stacks omits ("details omitted"); the proof is an inductive Cauchy lifting using the fact that $I^k$ is generated by degree-$k$ monomials in the $f_i$'s.
- L5: surjective image of a noetherian ring is noetherian (mathlib has this).
- Main: composition.

Total estimate ~150 LOC. Once the main lemma lands, the project's `_sub_lemma_L5_1_2_adicCompletion_noetherian` discharges in one line, and the higher-leverage propagation lemma `presheafValue_pairOfDefinition_isNoetherian` (~30-50 LOC) becomes accessible — this is the lemma round 3 identified as the single highest-leverage unblocker.

## 4. The 56-leaf chain — readiness audit summary

We grouped the 56 in-scope sorry leaves into nine clusters (A through L, omitting J and skipping out-of-scope H3/H4). Round 3 already had a per-cluster status table; the round-4 deltas are:

| Cluster | Round-3 status | Round-4 update |
|---|---|---|
| **A** (top-level wrappers) | A1/A2 parametric provable; A3 to be resolved | A3 keeps IsDomain (D-1); body still needs writing — to be a delegation to A1 |
| **B** (direct deps) | B1 needs C3+D8; B5 restated cover-level; B7/B8 chain blocked | B5 wrong-shape callers in audit-pass-2 wrappers identified (B-4 above); migration needed |
| **C** (Wedhorn-clean wrappers) | C1 needs Ex 6.38 + Lemma 8.31 assembly | Lemma 8.31 confirmed PROVED at parametric signature (3.1); C2 needs new combinator (D-2) |
| **D** (Wedhorn 7.40-7.52) | 10 leaves open; D9/D12/D14 flagged as API gaps | NEW B2: D9, D12 missing completeness hypotheses (3.4 items 1, 2); D14.3 new helper identified; D6 dead-code candidate |
| **E** (Wedhorn 6.18 chain) | E1 false (M̂ vs M fg); E3 mathlib gap (Stacks 0316) | E3 unblocked by 3.5; E4 realistic LOC revised upward (placeholder violation in L5.1.1 fixed) |
| **F** (Wedhorn 8.34 refinement tree, P3-P8) | 12 leaves; F5 suspect non-domain; F12 import-cycle | F5 keeps IsDomain (D-1 generalises); F12 to move (D-2) |
| **G** (restriction scaffolding) | G3 only; G1/G2 deleted | unchanged |
| **H** (Wedhorn 7.31, 7.32, 7.35) | H1 ~120 LOC; H2 finset form open | NEW B2: H-2 hidden CompactSpace (3.4 item 4) |
| **I** (Stacks 023N + Wedhorn 8.33) | I1 mathlib infra available; I2 needs case-split | NEW B2: I-2.3 Krull intersection FALSE non-domain non-unit (3.4 item 3) |
| **K** (mis-located) | K1 needs D10; K2 needs D7 | parametric restatement question raised |
| **L** (Wedhorn 8.31 wrappers) | DELETED, no consumers | **REPLACEMENT EXISTS** at parametric signature (3.1) |

Total remaining: same ~56 leaves; plus 5 new leaves in the Stacks 0316 sub-development; minus 1 placeholder violation fixed. The four hard mathlib gaps remain: Stacks 0316 (in progress, 3.5), MvPowerSeries Hilbert basis (subsumed by 3.5's L2), canonical valuation on complete Huber field (Q1 below), and the descent equaliser cocycle kernel for Stacks 023N (~50 LOC of mathlib glue).

## 5. Open questions for you

These are the eight specific questions for this round. Each can be answered in a paragraph or two.

**Q1 — Canonical rank-1 valuation on a complete non-archimedean Huber field.** The trivial-on-quotient valuation $v(a) = 0$ if $a \in \mathfrak{m}$, $v(a) = 1$ otherwise, lifting from $A/\mathfrak{m}$ is continuous on $A$ only if $\mathfrak{m}$ is *open*. For $\mathfrak{m}$ not open in $A$ (but still closed, in the complete Huber setting), we need a non-trivial valuation: the complete non-arch field $K := A/\mathfrak{m}$ has a *canonical* rank-1 topology valuation, and we lift it back to $A$. Mathlib has the `Valued K Γ` typeclass and the structure for valued fields, but no constructor "complete non-archimedean Huber field $\Rightarrow$ canonical rank-1 valuation". Three sub-questions:

(a) Is the right construction to follow Bourbaki, *Commutative Algebra*, Ch. VI §3.5 (composition / specialisation of valuations) plus completion functoriality, or the Engler-Prestel lattice-of-valuations argument (*Valued Fields*, §1.3)?

(b) Is there an easier route specifically for Huber fields (uniformiser-based, since a Tate field has a topologically nilpotent unit)?

(c) Or should the project sidestep this entirely? A cover-level argument using the existing project lemma `exists_spa_point_in_rationalOpen_of_isOpen_prime` plus power-bounded valuation criterion would avoid the construction altogether at the cost of routing 7.51(2) through 7.45 + 7.41, but we are not sure whether the cover-level form actually contains the maximal-ideal case.

**Q2 — F12 file refactor.** We propose to move the four declarations `tateAcyclicity` (the conjunction of separation and gluing), `tateAcyclicity_gluing_via_refinement`, `rationalCovering_hasSeparation`, and `rationalCovering_hasGluing` from `LaurentRefinement.lean` into `TateAcyclicityFinalAssembly.lean`. The reason is the import cycle: `Cor832.lean` (where the clean Wedhorn 8.32 product faithful flatness combinator will live) imports `LaurentRefinement.lean`, so the gluing proof, which uses Cor 8.32, cannot stay in `LaurentRefinement.lean`. Is this the right architectural fix? Cleaner alternatives we considered:

(a) Split `LaurentRefinement.lean` into a "data + setup" file and an "acyclicity output" file, so the latter can sit downstream of Cor832.
(b) Keep `tateAcyclicity` in `LaurentRefinement.lean` and route Cor832's faithful flatness through a different intermediate (e.g., an existence-only statement that pushes the heavy lifting upstream).
(c) Move only `tateAcyclicity` (not the `rationalCovering_*` wrappers, which would re-export downstream).

Our default is the straight move (the four declarations as a unit); we'd value your sanity-check.

**Q3 — Spa.comap framework (`Spa_presheafValue_eq_rationalOpen`).** The pullback $\mathrm{Spa}\,\varphi : \mathrm{Spa}\,B \to \mathrm{Spa}\,A$ of a continuous ring map $\varphi : A \to B$ exists in the project axiom-clean. What's missing is the image identification: for $D = (T, s)$ a rational locale datum, $\mathrm{Spa}\,(\mathcal{O}_X(D), \mathcal{O}_X(D)^{+}) \cong R(T/s) \subset \mathrm{Spa}\,A$ via the comap of $\mathrm{algebraMap}\,A\,\mathcal{O}_X(D)$. We estimate ~500 LOC for the full identification, including the inverse map (extending a valuation on $A$ that's well-defined on $T/s$ to a valuation on $\mathcal{O}_X(D)$ via the localisation universal property + completion). Two sub-questions:

(a) Is this the right project-internal sub-development scope, or should we supply the equivalence as a parametric hypothesis on the IsSheafy theorem and defer the construction?

(b) Wedhorn's 8.2 proof uses the "Hauptmodul" (universal property of the rational localisation). Is mathlib's `Valuation.IsEquiv` + the existing `Spv.comap_continuous` infrastructure enough, or are there specific Spv-equivalences (`Spv.IsEquiv.of_rationalSubset_membership` style) that mathlib doesn't have?

**Q4 — Krull intersection in non-domain Tate.** The project's `laurentCover_exact_general` (Wedhorn 8.33) drops `[IsDomain A]` and relies on $\bigcap_n (f)^n = 0$ for arbitrary $f \in A$ in noeth complete Tate. We confirmed this is FALSE for non-domain $A$ (counterexample $\mathbb{Q}_p \times \mathbb{Q}_p$ with $f = (p, 0)$, since the idempotent annihilator $(0, 1)$ gives intersection $\supseteq \{(0, c)\}$). Two routes:

(a) Re-add `[IsDomain A]` to the 8.33 statement, matching F4's hypothesis bundle (and the user's decision in 3.3 to keep `IsDomain` throughout).

(b) Replace the Krull route with a different Tate-topological injectivity argument for the non-unit non-domain case. We do not know of one.

In Wedhorn's own 8.33 proof (p. 83), is the domain hypothesis implicit (perhaps from his strong-noetherian Tate setting), or does he handle the non-domain case via a different argument?

**Q5 — Cluster L completeness.** We have confirmed that the three deleted L-cluster wrappers have replacements at the parametric signature, all PROVED axiom-clean. Is this complete for the Wedhorn 8.31 facet of the project, or are there other 8.31 forms we will need downstream (for example, a non-tate-but-noetherian Banach setting where the parametric ring-of-definition shape doesn't apply, or a Banach-normalised flatness statement we might want in a future iteration)?

**Q6 — Path α discharge sequence.** We propose to write a fresh combinator `cor_8_32_clean_via_laurent` in `TateAcyclicityFinalAssembly.lean` that takes a per-cover Laurent witness (i.e. for each cover piece $D \in C.\mathrm{covers}$, an exhibition of $D$ as a Laurent-minus datum) and uses the Wedhorn-honest `flat_over_base_tate_laurent` + the abstract product faithful flatness combinator. After the F12 move (Q2), the gluing proof for `tateAcyclicity` Part 2 then uses this combinator + the Stacks 023N descent equaliser already in the project. Is there a cleaner path? A reduction-to-standard-cover-first approach via Wedhorn 7.54 + a per-leaf direct argument might avoid the per-cover Laurent witness entirely.

**Q7 — Stacks 0316 routing.** Our skeleton uses the "direct" route from Stacks (pick generators $f_1, \ldots, f_n$ of $I$, build the evaluation $R \llbracket X_i \rrbracket \to \widehat{R}$, $X_i \mapsto f_i$, show surjective). This requires the multivariate Hilbert basis (sub-developed as L2 via iterated single-variable Hilbert), the eval map L3, and the surjectivity workhorse L4. The alternative is the gr-filtration route (Stacks 05GH = "more general" version that needs only $R/I$ noeth and $I$ f.g.): construct $\mathrm{gr}_I R$, show it is noeth via the surjection from $R/I[T_1, \ldots, T_t]$, lift homogeneous generators back via completeness. The latter is more general but requires the $\mathrm{gr}_I$ machinery and an absolute-summability lemma in adic completions, neither of which is in mathlib. We chose the direct route for ~150 LOC over the gr route for ~300 LOC. Is that the right call?

**Q8 — L5.1.1 ring iso encoding.** The fixed statement of the project's L5.1.1 says: there is a ring isomorphism

$$\mathrm{TateAlgebra}\,A \cong (P.A_0 \otimes A) \otimes_{P.A_0} \widehat{P.A_0[X]}$$

where the right hand side is the base change to $A$ of the $P.I$-adic completion of the polynomial ring $P.A_0[X]$. This expresses Wedhorn Remark 6.37(3): $A\langle X \rangle$ as the $I$-adic completion of $A_0[X]$ in the project's encoding. Is this the right encoding, or is there a simpler equivalent form (e.g. directly as $A \otimes_{A_0} \widehat{A_0[X]}$ without the intermediate $P.A_0 \otimes A$ factor)? The intermediate factor was there to make the base-change explicit, but it may be redundant.

## 6. What the brief is NOT asking about

To save your time:

- We are not re-litigating Path α — round 3 settled that.
- We are not asking about the F-cluster's P3-P8 internal mechanics; round 3 already validated the refinement-tree decomposition and our internal review found no new B2s there.
- We are not asking about whether `IsStronglyNoetherian` is the right framing; round 3 settled that.
- We are not raising D9 or D12 as open questions; we will simply add the missing completeness hypotheses (you confirmed in Q-S24.4 that the headline theorem takes completeness; the same reasoning makes D9/D12 take it locally).
- We are not asking about Cluster H's H3/H4 (Wedhorn 7.35 in the SpvAI setting) — those are explicitly out of scope.

## 7. Document metadata

- Project name: Adic spaces (Wedhorn's *Adic Spaces*, arXiv:1910.05934, Lean 4 / Mathlib v4.29.0-rc6)
- Brief generated: 2026-05-18
- Round: 4 (Session 26)
- Length: ~3,800 words
- Build status at writing: `lake env lean` clean on the two newly-touched files (`AdicCompletionNoetherian.lean` (new), `WedhornStronglyNoetherian.lean` (L5.1.1 fixed)); sorry warnings only. `lake build` not exhaustively re-run.
- Recent commit context: relocate `exists_spa_point_in_rationalOpen_of_prime` (StructureSheaf); Wedhorn 7.45 audit-pass-2 wrapper delegation (WedhornStronglyNoetherian); AuditCleanWrappers — 3 sorries delegated to canonicals; K.1.a, K.1.b, K.1 faithfully-flat descent equaliser closed.
- Prior briefs: 2026-05-18 (round 1 of today), 2026-05-18-2 (round 2), 2026-05-18-3 (round 3 — your reply settled Path α). This is round 4.
- Audit substrate: project audit document (master adversarial findings), decomposition (Sessions 21-26), B2 log (26 entries, last 7 from Session 26).

— *End of brief —*
