# Decomposition — Campaign 5: the adic Fargues–Fontaine curve (definition layer)

**Status: APPROVED 2026-07-24 (owner sign-off; skeleton build-verified green).**
Written 2026-07-24 by `/develop`. Companion files: `plan.md`, `tickets.md`,
`chatgpt-packet-fargues-fontaine-plan-2026-07-24.md` (external-review packet; see §0.3).

## §0. Provenance, priors, external review

### §0.1 Primary source and the faithfulness anchor

Primary source: **[BFHHLWY]** C. Birkbeck, T. Feng, D. Hansen, S. Hong, Q. Li, A. Wang,
L. Ye, *Extensions of vector bundles on the Fargues–Fontaine curve*, arXiv:1705.00710v3
(local: `refs/AdicSpaces/1705.00710-BFHHLWY-extensions-ff-curve.pdf`), **Definition
2.1.1, p. 6** (verbatim):

> Let E be a finite extension of **Q**_p, with uniformizer π, ring of integers E°, and
> residue field **F**_q where q = p^f, and let F/**F**_q be an algebraically closed
> perfectoid field, with ring of integers F° and pseudouniformizer ϖ.
> Let W_{E°}(F°) = W(F°) ⊗_{W(**F**_q)} E° be the ramified Witt vectors of F° with
> coefficients in E°. Define
>     𝒴_{E,F} = Spa(W_{E°}(F°)) \ {|p[ϖ]| = 0},
> and let φ : 𝒴_{E,F} → 𝒴_{E,F} be the Frobenius automorphism of 𝒴_{E,F} induced by the
> natural q-Frobenius φ_q = φ^f ⊗ 1 on W_{E°}(F°). The (mixed-characteristic) *adic
> Fargues-Fontaine curve* 𝒳_{E,F} is
>     𝒳_{E,F} = 𝒴_{E,F}/φ^**Z**.

And **Proposition 2.1.2** (p. 6): "**(Kedlaya).** For any pair (E,F) as above, 𝒳_{E,F}
is a Noetherian adic space over Spa E. *Proof.* This is one of the main results of
[Ked16]. □"

**Scope anchor.** The paper itself splits "the definition" (Def 2.1.1: a quotient of a
subspace of an adic spectrum by a group action) from "the quotient is a Noetherian adic
space" (Prop 2.1.2, delegated wholesale to Kedlaya). This campaign formalises the
content of **Def 2.1.1** — the spaces, the action, and every point-set fact needed for
the quotient to be honest (covering, proper discontinuity, freeness, open quotient map,
chart embeddings, quasicompactness). The analogue of Prop 2.1.2 (structure
presheaf/sheafiness on 𝒳) is explicitly a **follow-on campaign**, mirroring the paper's
own division of labour.

Secondary sources (construction detail the paper deliberately omits — §2.1 opens "we
content ourselves with giving just a cursory introduction to the construction", so per
the source-gap fallback chain the proofs are drawn from):

- **[Ked-AWS]** Kedlaya, *Sheaves, stacks, and shtukas*, AWS 2017 notes (local:
  `refs/AdicSpaces/kedlaya-aws-sheaves-stacks-shtukas.pdf`), §3.1 — Definition 3.1.2,
  Definition 3.1.5, **Remark 3.1.9** (the covering; quoted at R3 below), Remark 3.1.10,
  Remark 3.1.11.
- **[SW]** Scholze–Weinstein, *Berkeley Lectures on p-adic Geometry* (local:
  `refs/AdicSpaces/scholze-weinstein-berkeley-lectures.pdf`), §12.2 (κ, κ∘φ = pκ,
  the four special points), §13.1 ("(p,[p♭])-adic topology"), Definition 13.5.1.
- **[Bhatt]** Bhatt, *Lecture notes for a class on perfectoid spaces* (local:
  `refs/AdicSpaces/bhatt-679-perfectoid-lectures.pdf`), §3.1–3.2 (perfectoid fields of
  char p; Corollary 3.2.3 completeness pattern).
- **[KL15]** Kedlaya–Liu, *Relative p-adic Hodge theory: Foundations* (local:
  `refs/AdicSpaces/kedlaya-liu-relative-padic-hodge-1301.0792.pdf`), §8.7 (corroboration;
  their construction is via extended Robba rings, not mirrored here).
- **[Ked16]** Kedlaya, *Noetherian properties of Fargues–Fontaine curves* (local:
  `refs/AdicSpaces/kedlaya-noetherian-ff-curves-1602.06899.pdf`) — reserved for the
  follow-on campaign (Prop 2.1.2 layer); not load-bearing here.
- **[FF]** Fargues–Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*
  (local: `refs/AdicSpaces/fargues-fontaine-courbe.pdf`) — reserved for the stretch
  nonemptiness leaf (§1.4, multiplicative Gauss norms).

### §0.2 Scope decisions (deliberate deviations from Def 2.1.1, each justified)

- **D1 (E = Q_p).** Def 2.1.1 is stated for general E/Q_p via ramified Witt vectors
  W_{E°}(F°) = W(F°) ⊗_{W(F_q)} E°. Mathlib has no ramified Witt vectors and no
  canonical W(F_q)-algebra structure on E°; building them is a separate project. We
  formalise the case **E = Q_p** (q = p, f = 1, W_{E°}(F°) = W(F°), φ_q = the Witt
  Frobenius), which is the definition verbatim at that specialisation. File layout keeps
  a `FarguesFontaine/` namespace so general E slots in beside it later.
- **D2 (F generalised).** Def 2.1.1 takes F algebraically closed. Algebraic closedness
  is not used anywhere in the construction of 𝒴, φ, 𝒳 — [Ked-AWS, Hyp. 3.1.1 +
  Rem. 3.1.9] runs for any perfectoid Tate R (a fortiori any perfectoid field) of char
  p, and [KL15 §8.7] for perfectoid Banach algebras. We state everything for
  `IsPerfectoidField p F` + `CharP F p` (maximal-generality rule); the alg. closed case
  is an instance.
- **D3 (topological layer now, presheaf later).** See §0.1 scope anchor.
- **D4 (windows in cleared-integer form).** [Ked-AWS, Rem. 3.1.9] writes rational
  exponents (`v(p)^{cp^n} ≤ v(ϖ)`). Rational powers of values are not literal objects in
  a general value group; the standard reading (and the only one that type-checks) clears
  denominators using multiplicativity and `[ϖ]^m = [ϖ^m]`. Our `KGE`/`KLE` predicates
  are exactly that reading; the Lean ↔ source match paragraphs at R3 record it.
- **D5 (action convention).** The project's `ValuationSpectrum` action is
  `g • v = comap (g⁻¹) v = v ∘ φ^{-g}`, under which κ(g•v) = κ(v)/p^g and windows shift
  **down**: `φ^k(U_n) = U_{n-k}`. [SW §12.2] uses the pushforward convention (κ∘φ = pκ,
  windows shift up). Same orbits, same quotient; the sign is recorded in
  `zsmul_windowU`'s docstring.
- **D6 (ϖ-independence).** Def 2.1.1 fixes one ϖ. We add `Y_indep` (the space is
  unchanged under a different pseudo-uniformizer) as sanity API mirroring [Ked-AWS
  §11.2]'s independence remark, but do NOT formalise "the curve is independent of ϖ up
  to canonical homeomorphism" in this campaign (a `Quotient`-transport statement of no
  mathematical content beyond `Y_indep`; deferred).

### §0.3 External review status (owner-requested: gpt-5.6-sol) — **DELIVERED**

After seven failed MCP attempts (root cause diagnosed: the MCP server's 5-minute
`execFile` timeout killed every max-effort run; the "models-manager" stderr line was a
red herring; server patched to 40 min on 2026-07-24), the as-built packet was delivered
by DIRECT codex invocation (`CODEX_HOME=~/.codex2`, gpt-5.6-sol, max reasoning).
**Full verbatim reply: `chatgpt-reply-fargues-fontaine-2026-07-24.md`.** Verdicts:

- Q1 (window arithmetic incl. higher-rank, boundaries, k<0): **SOUND** — recomputed
  independently; only discreteness of ℤ is used, no Archimedean property.
- Q2 (A_inf completeness): **GAP — accepted and repaired.** "Separate p-adic and
  ϖ-adic completeness ⟹ completeness for pⁿA+[ϖ]ⁿA" does not follow (a J-Cauchy
  sequence need not be Cauchy in either direction; Witt addition is not digit-wise);
  moreover the previously-documented fallback `W(R) = lim_m W(R/ϖ^m)` is ALSO
  insufficient (not cofinal: pⁿA leaves high digits uncontrolled). The repaired route
  (now binding, see L2.7/L2.8): truncate in the p-direction first.
- Q3 (O_F ϖ-adic + complete, no valuation-ring input): **SOUND** — works for any
  complete uniform Tate ring; F° is an open, hence closed, subgroup.
- Q4 (strictness): **SOUND** — force N ≥ 2 in the proof; NOTE: `v ≤ 1` on all of
  A_inf is not needed anywhere in the window arguments (only continuity +
  nonvanishing + topological nilpotence of p, [ϖ]).
- Q5 (silent assumptions): **GAP — explicitness checklist**, integrated into tickets:
  supp-primality product-splitting; power-cancellation/strict-mono on NONZERO values;
  two-sided pseudouniformizer comparison (ϖ^r = ϖ'a AND ϖ'^s = ϖb); φ-stability of 𝒴
  in BOTH directions; Spa-functoriality of automorphisms as homeomorphisms;
  q⁻¹(q(O)) = ⋃ gO for the open quotient; T0 is subspace-hereditary and local for
  open covers. **Compactness warning:** a bare basic-open trace is NOT quasicompact —
  𝒴 itself is such a trace and is not qc — so T505 must use the genuine
  Boolean-embedding criterion (windows are affinoid in the classical picture, 𝒴 is
  not; cf. [Ked-AWS Rem. 3.1.9 vs 3.1.11]).
- Q6 (c = (p+1)/2): **SOUND**, loses nothing for this campaign.
- Q7 (quotient pathologies): **SOUND** — no point-set obstruction; sol's naming
  guidance: this layer is "the underlying topological orbit space of the adic
  Fargues–Fontaine curve"; adic-space-hood, spectrality, sobriety, Noetherianity are
  NOT to be inferred from the orbit quotient (they are the follow-on campaign, as
  planned per D3).

Sol's bottom line, verbatim: "proof-filling can proceed after repairing item 2 and
making the item 5 dependencies explicit; the window statements themselves do not need
redesign."

### §0.4 Prior-B2 log consultation (Step 4.6 — binding)

`b2_log.jsonl` read in full: 74 entries. Zero matches — by name or by shape — for any
leaf below (searched: witt, perfectoid, frobenius, fargues, teichmuller; all entries
concern the Wedhorn-8.28/FJP campaigns' Tate-algebra and sheafiness statements, none
touching Witt vectors, perfectoid fields, group actions, or quotients). **Every leaf:
clean of prior B2 history.** (Recorded once here; per-leaf blocks omit the field.)

### §0.5 Skeleton location

The Lean skeleton (every leaf stated, `:= by sorry`) lives in
`projects/AdicSpaces/Adic spaces/FarguesFontaine/`:
- `PerfectoidFieldCharP.lean` (R1 leaves L1.*)
- `AinfHuber.lean` (R1 leaves L2.*)
- `FrobeniusAction.lean` (R2 leaves L3.*)
- `YSpace.lean` (R3 leaves L4.*, L5.*)
- `Curve.lean` (R4–R5 leaves L6.*, L7.*)
plus: legacy `Adic spaces/FarguesFontaine.lean` **deleted** (see §5 takeover verdict),
root `Adic spaces.lean` imports swapped, and `ValuationAction.lean` generalised (unused
`[Finite G]` dropped from the `GroupAction` section — L3.6).
`lake build '«Adic spaces»'` status: **GREEN, verified 2026-07-24** — zero errors
across the full library (so the ValuationAction generalisation broke no consumer);
sorry-token inventory in the five skeleton files: PerfectoidFieldCharP 9, AinfHuber 10,
FrobeniusAction 9, YSpace 23, Curve 15. `instMulSemiringActionAinf` and
`instPlusSubringAinf` compiled sorry-FREE (real data, as required for downstream
definitional transparency).

---

## §1. R1 — A_inf = W(O_F) is a complete Huber ring, its own ring of integral elements

### Plain-English proof (Step 1; sources: [Ked-AWS Def 3.1.2], [SW §13.1], [Bhatt §3.1–3.2])

Let F be a perfectoid field of characteristic p, O_F = F° its power-bounded subring, ϖ a
pseudo-uniformizer (a topologically nilpotent unit; it is power-bounded, so ϖ ∈ O_F).
O_F is a domain (subring of a field) of characteristic p. It is perfect: Frobenius is
injective on any domain of characteristic p, and surjective because the perfectoid
axiom supplies for each power-bounded x a power-bounded y with x = y^p + p·z = y^p
(char p). Since F is Tate and uniform with O_F bounded and open, the sets ϖ^n·O_F form
a neighbourhood basis of 0 in O_F; F is complete, O_F ⊆ F is closed, so O_F is
ϖ-adically separated and complete ([Bhatt, Cor. 3.2.3] pattern).

Now A := W(O_F). Give it the (p,[ϖ])-adic topology ([SW §13.1]: "A_inf = W(O_{C♭}),
with its (p,[p♭])-adic topology"). The ideal I = (p,[ϖ]) is finitely generated, so A is
a Huber ring with pair of definition (A, I); A is its own ring of integral elements
(⊤ is integrally closed, open, and every element of an adic ring is power-bounded). For
completeness ([Ked-AWS Def 3.1.2]: "It is complete for the adic topology defined by the
inverse image of some ideal of definition of R⁺"), sandwich the I-adic filtration
between the "product" filtrations: I^{2n} ⊆ (p)^n + ([ϖ])^n ⊆ I^n. A Cauchy sequence
for the product filtration is, in each Witt coordinate, a ϖ-adically Cauchy sequence of
elements of O_F (Teichmüller multiplication acts coordinatewise: ([ϖ]·y).coeff i =
ϖ^{p^i}·y.coeff i), and W(O_F) is p-adically complete (mathlib,
`WittVector.isAdicCompleteIdealSpanP`, O_F perfect); combining the two directions
produces the limit, and separatedness follows from ⋂ (p^n) = 0 levelwise plus ϖ-adic
separatedness of O_F.

Pointers into the source: [Ked-AWS] p. 66, Definition 3.1.2 (one sentence — the
completeness assertion); [SW] p. 108, §13.1 first paragraph (the topology); [Bhatt]
p. 12, Corollary 3.2.3 (the O_F-level completeness, for the tilt — same argument);
mathlib `Mathlib/RingTheory/WittVector/Complete.lean` (the p-direction, fully proven).
The fine structure of the completeness proof is genuinely terse in all sources (each
asserts it in a sentence); the coefficientwise expansion above is our own, per the
source-gap rule, and is the single largest residual risk of the campaign (§6, RR1).

### Leaves (Lean names in `PerfectoidFieldCharP.lean` unless said otherwise)

- **L1.1** (leaf, mathlib): `instance : IsDomain (OF F)`
  - Source claim: implicit in [BFHHLWY Def 2.1.1] ("ring of integers F°" of a field).
  - Discharge: `Subring.instIsDomain` (subring of a field is a domain).
  - Attacks: [1] counterexample: none possible — subring of a field; [2] edge: F = F_p
    is excluded (not Tate: no topologically nilpotent unit ≠ 0? F_p discrete IS
    excluded by `IsPerfectoidField`'s Tate axiom — consistent); [3] discharge check:
    mathlib instance exists for subrings of division rings. SURVIVED.
- **L1.2** (leaf, mathlib): `instance : CharP (OF F) p`
  - Source: setting of [BFHHLWY Def 2.1.1] (F/F_q).
  - Discharge: char of subring = char of field (`CharP.subring`-shape; verify exact name
    at fill time — if absent, `charP_of_injective_ringHom` on `Subring.subtype`).
  - Attacks: [1] no counterexample (injection reflects char); [2] edge p = 2 fine;
    [3] hypothesis: needs only `CharP F p` ✓. SURVIVED.
- **L1.3** (leaf, project): `frobenius_surjective_OF`
  - Source claim (verbatim, [Bhatt] p. 9–10, Example 3.1.2(3)):
    > "Let K be a NA field of characteristic p. Then K is perfectoid if and only if K is
    > perfect. In this case, semiperfectness of K° implies its perfectness…"
  - Lean ↔ source: our statement is the "semiperfectness of K°" direction made explicit:
    surjectivity of `frobenius (OF F) p`. The project class field
    `IsPerfectoidRing.frobenius_surj` gives x = y^p + p·z with y,z power-bounded;
    `CharP F p` kills p·z. Match is exact.
  - Discharge: project `IsPerfectoidRing.frobenius_surj` (PerfectoidRing.lean:66–92
    class field, verified present by audit) + `CharP.cast_eq_zero`.
  - Attacks: [1] counterexample: a NON-uniform Tate field of char p with non-perfect F°?
    Excluded — the class bundles uniformity; [2] hypothesis-strength: does surjectivity
    on F° need the ϖ^p ∣ p field? No — only frobenius_surj + char p; [3] source-drift:
    Bhatt says semiperfect ⟹ perfect for K° — we only re-prove semiperfectness here;
    injectivity is L1.4's business. SURVIVED.
- **L1.4** (leaf, mathlib+L1.3): `instance instPerfectRingOF : PerfectRing (OF F) p`
  - Source: [Bhatt, Ex. 3.1.2(3)] as above ("implies its perfectness").
  - Discharge: `PerfectRing.ofSurjective`-shape from L1.3 + injectivity of Frobenius on
    reduced rings (`frobenius_inj` for domains/reduced; verify exact mathlib name).
  - Attacks: [1] injectivity could fail for non-reduced — O_F is a domain (L1.1);
    [2] discharge: `PerfectRing` in mathlib is stated as `Bijective (frobenius R p)` via
    a class with `bijective_frobenius`; constructor from bijectivity exists
    (`PerfectRing.ofBijective`? verify); [3] edge: trivial ring excluded (field ≠ 0).
    SURVIVED.
- **L1.5** (leaf, project): `PseudoUniformizer.toOF` (definition, sorry-free) and
  `PseudoUniformizer.toOF_ne_zero`
  - Source: [BFHHLWY Def 2.1.1] ("pseudouniformizer ϖ", an element of F°).
  - Discharge: definition assembled from `PseudoUniformizer.isTopologicallyNilpotent` +
    `IsTopologicallyNilpotent.isPowerBounded` (both in project, audit-verified);
    nonzeroness: ϖ is a unit of the field F, units are nonzero, `Subtype.ext`.
  - Attacks: [1] is a topologically nilpotent UNIT automatically power-bounded? Yes —
    project lemma, audit-verified at Bounded.lean:208; [2] degenerate F: a field with
    the discrete topology has no pseudo-uniformizer (0 is not a unit) — consistent with
    Tate; [3] drift: none, mechanical. SURVIVED.
- **L1.6** (leaf, project+mathlib): `span_toOF_pow_mem_nhds_zero`,
  `exists_span_toOF_pow_subset_nhds`
  - Source claim ([SW] p. 92, §11.2, for the analogous R⁺): the topology of a perfectoid
    Tate ring restricted to R⁺ is the ϖ-adic one; standard Tate-ring fact ([Wedhorn]
    §5.30-shape: for a Tate ring with ring of definition A₀ ∋ ϖ, {ϖ^n A₀} is a basis).
    Project-side: `IsPerfectoidRing` bundles uniformity, so O_F = F° is bounded and
    open; ϖ^n·O_F ∈ 𝓝 0 because ϖ^n is a unit times an open subgroup… precise route:
    O_F open (power-bounded subring of uniform Tate ring is open — project has the
    uniformity class exactly for this) and multiplication by the unit ϖ^n is a
    homeomorphism of F carrying O_F to ϖ^n O_F; conversely boundedness of O_F +
    topological nilpotence of ϖ gives ϖ^n O_F ⊆ U eventually.
  - Discharge: project `IsBounded` (Bounded.lean:83), `IsTopologicallyNilpotent`
    definitional unfolding (`tendsto`), `Homeomorph.mulLeft₀`-shape from mathlib for
    unit multiplication, openness of `powerBoundedSubring` from `IsUniform` — the
    precise openness lemma must be located in Uniform.lean at fill time; if the project
    lacks "O_F is open", it is a genuine sub-leaf: openness of F° for a uniform Tate
    ring, one paragraph from `IsUniform.isBounded_powerBounded` + ring-of-definition
    membership. Flagged as the only L1-family sub-risk.
  - Attacks: [1] counterexample: non-uniform Tate ring where F° is NOT open — excluded
    by the uniformity field; [2] direction check: both directions stated separately
    (∈ 𝓝 0, and ⊆ U eventually) — no circularity; [3] hypothesis: does L1.6 need
    perfectoid, or just uniform Tate? Just uniform Tate + pseudo-uniformizer — the
    statements are placed with the perfectoid variable block for campaign locality but
    generalise; noted for the `/generalise` lane later. SURVIVED (with the sub-risk
    note).
- **L1.7** (leaf, project): `isHausdorff_span_toOF`
  - Source: [Bhatt, Cor. 3.2.3] (verbatim):
    > "With t as above, K°♭ is t-adically complete, and that the t-adic topology
    > coincides with the given topology."
    (Bhatt states it for the tilt's integer ring K°♭ = lim K°/π; for our F of
    characteristic p the same statement reads off for O_F itself; completeness of a
    char-p perfectoid field's O_F is the degenerate case of his diagram where the limit
    is along x ↦ x^p on K° itself. The match paragraph for L1.8 covers both.)
  - Lean ↔ source: `IsHausdorff (span {ϖ}) (OF F)` = "t-adic topology separated", the
    separatedness half of "complete" in Bhatt's convention (his "complete" includes
    separated, cf. [Ked-AWS Convention 0.0.1]).
  - Discharge: from L1.6 + `T0Space F` (class field `t0`) via: x ∈ ⋂ ϖ^n O_F ⟹ x in
    every neighbourhood of 0 ⟹ x = 0 by T0 for topological groups. Mathlib bridge:
    `IsHausdorff` is `∀ x, (∀ n, x ≡ 0 [SMOD I^n]) → x = 0` — direct.
  - Attacks: [1] SMOD vs set-membership mismatch — `Ideal.span {ϖ}^n • ⊤` vs `ϖ^n O_F`:
    `smul_eq_mul` + `Ideal.span_singleton_pow`; mechanical but listed; [2] T0 vs T2:
    only T0 needed for groups (T0 group ⟹ T2, but we don't even need that); [3] edge:
    ϖ nilpotent? ϖ is a unit-image, nonzero in a domain, and topologically nilpotent —
    no contradiction (F is not discrete). SURVIVED.
- **L1.8** (leaf, project): `isAdicComplete_span_toOF`
  - Source: [Bhatt, Cor. 3.2.3] verbatim as in L1.7.
  - Lean ↔ source: Bhatt's proof compares inverse systems K°♭/(t^{p^n}) ≅ K°/π-towers;
    for char-p F the content is: O_F closed in complete F, and the ϖ-adic and subspace
    topologies agree (L1.6), so ϖ-adic Cauchy ⟹ converges in F, limit power-bounded,
    convergence is ϖ-adic. Our statement `IsAdicComplete (span {ϖ}) (OF F)` is precisely
    "t-adically complete".
  - Discharge: L1.6 + `CompleteSpace F` (class field) + closedness of O_F
    (power-bounded subring is closed in a uniform T0 Tate ring — check project; if
    absent, sub-leaf: limits of power-bounded sequences are power-bounded, which the
    audit found as `isPowerBounded_of_tendsto_of_powerBounded` in PerfectoidRing.lean —
    verified present) + `IsAdicComplete` constructor from sequential limits
    (`IsPrecomplete` via project `AdicConvergence` API).
  - Attacks: [1] trap: IsAdicComplete over non-noetherian rings — no pathology here
    since we verify the limit directly, not via completion functors; [2] uniform-space
    vs adic mismatch: both directions of L1.6 are exactly what is needed; [3] discharge
    names: `isPowerBounded_of_tendsto_of_powerBounded` audit-verified. SURVIVED.
- **L2.1** (leaf, mathlib): `teichPi` (def) + `teichPi_pow` + `teichPi_ne_zero`
  - Source: [BFHHLWY Def 2.1.1] (the element [ϖ]); [Ked-AWS Rem. 3.1.9 footnote-level]:
    rational exponents cleared "via [ϖ^n] = [ϖ]^n" (our gloss D4).
  - Discharge: `WittVector.teichmuller` is a `MonoidHom` (mathlib): `map_pow` gives
    `teichPi_pow`; `teichmuller_ne_zero`-shape via coeff 0 (project
    WittVectorPrimitive.lean has `coeff_zero_ne_zero_of`-adjacent API; or
    `WittVector.teichmuller_coeff_zero` + L1.5).
  - Attacks: [1] [x]·[y] = [xy] needs commutativity of coefficients ✓; [2] ne_zero needs
    O_F nontrivial ✓ (domain with 1 ≠ 0); [3] drift: none. SURVIVED.
- **L2.2** (leaf, mathlib): `instTopologicalSpaceAinf` (def, sorry-free) +
  `instIsTopologicalRingAinf`
  - Source: [SW §13.1] (verbatim): "let A_inf = W(O_{C♭}), with its (p, [p♭])-adic
    topology."
  - Lean ↔ source: `Ideal.adicTopology (Iinf … canonical-ϖ)`. The instance fixes the
    canonical Tate pseudo-uniformizer; L2.3 restores ϖ-freedom. SW's [p♭] is one choice
    of ϖ; D6 covers the discrepancy.
  - Discharge: `Ideal.adicTopology` (mathlib); ring-topology via the
    `RingSubgroupsBasis.toRingFilterBasis` route used inside
    `Mathlib/Topology/Algebra/Nonarchimedean/AdicTopology.lean` (the `isAdic_iff` proof
    at :177–178 shows the pattern; exact instance-producing spelling to be fixed at fill
    time — possibly `RingSubgroupsBasis.instTopologicalRing`-shape).
  - Attacks: [1] a DIFFERENT topology on `WittVector` from elsewhere could clash — grep:
    the only other instance lived in the deleted legacy file (p-adic; §5); mathlib has
    none; [2] diamond with `OF`'s topology: `WittVector p (OF F)` carries no inherited
    topology (WittVector is a structure wrapper) — no diamond; [3] the instance picks
    canonical ϖ — independence is L2.3, and no lemma below ever needs definitional
    equality with a specific ϖ's ideal. SURVIVED.
- **L2.3** (leaf, project): `isAdic_Iinf`
  - Source ([Ked-AWS] p. 92, §11.2, verbatim, for the analogous independence):
    > "Note that this is independent of the choice of ϖ, as for any other choice ϖ',
    > there is some n such that ϖ|(ϖ')^n and ϖ'|ϖ^n."
  - Lean ↔ source: `IsAdic (Iinf ϖ)` for every ϖ, against the canonical-ϖ instance
    topology, is exactly "the (p,[ϖ])-adic and (p,[ϖ'])-adic topologies coincide",
    reformulated via mathlib's `isAdic_iff` (two inclusions of filtrations). The
    divisibility: ϖ'^n ∈ ϖ·O_F for some n (both topologically nilpotent units; L1.6's
    basis + unit trick), then [ϖ']^n = [ϖ'^n] = [ϖ]·[ϖ'^n/ϖ] ∈ ([ϖ]).
  - Discharge: L2.1 (`teichPi_pow`), `Ideal.pow_le_pow_right`-style monotonicity,
    `isAdic_iff` (mathlib, AdicTopology.lean:161).
  - Attacks: [1] does ϖ | ϖ'^n really hold in O_F for ANY two pseudo-uniformizers of a
    perfectoid field? Yes: ϖ'^n → 0 topologically, so ϖ'^n ∈ ϖ·O_F for n large since
    ϖ·O_F ∈ 𝓝 0 (L1.6) — no valuation-ring input needed; [2] the ideals (p,[ϖ]) and
    (p,[ϖ']) need MUTUAL cofinality of powers, with the p-generator shared — the
    monomial expansion needs (p,[ϖ])^{2n} ⊆ (p,[ϖ'])^n-type bounds: each monomial
    p^a[ϖ]^b with a+b ≥ 2n has a ≥ n or b ≥ n, and [ϖ]^n ∈ ([ϖ']^m…) — routine but the
    exponent bookkeeping is a real 20-line proof, sized accordingly; [3] drift: source
    speaks of the LOCUS independence; the topology independence is the same divisibility
    (recorded as our gloss). SURVIVED.
- **L2.4** (leaf, project): `instIsHuberRingAinf`
  - Source: [Ked-AWS Def 3.1.2] (A_inf topologised adically by a f.g. ideal) +
    [SW §13.1].
  - Discharge: project `IsHuberRing` via `PairOfDefinition` with A₀ = ⊤, I = Iinf
    (transport along `Subring.topEquiv` for the ideal-of-⊤ friction), `fg` = span of a
    2-element set (`Set.Finite.toFinset`-shape), `isAdic` = L2.3 at canonical ϖ,
    `isOpen` = ⊤.
  - Attacks: [1] A₀ = ⊤ admissible? `PairOfDefinition` (HuberRings.lean:57) requires
    `A₀ : Subring A` open with I : Ideal A₀ f.g. adic — ⊤ qualifies; the ⊤-transport is
    bookkeeping; [2] completeness NOT required by the class (audit-verified) ✓;
    [3] discharge: all fields verified to exist by the API survey. SURVIVED.
- **L2.5** (leaf, project): `instPlusSubringAinf` (sorry-free), `isPowerBounded_Ainf`,
  `isAffinoidRing_Ainf`
  - Source: [Ked-AWS Def 3.1.5 / Rem. 3.1.9] — the pair is Spa(A_inf, A_inf); [BFHHLWY
    Def 2.1.1] writes Spa(W_{E°}(F°)) (self-pair, standard reading — W_{E°}(F°) is its
    own ring of integral elements, as in [SW §13.1] Spa A_inf).
  - Lean ↔ source: `PlusSubring := ⊤` and `IsAffinoidRing` (= ⊤ open, integrally closed,
    ⊆ power-bounded) formalise "Spa(A_inf, A_inf)" with A_inf⁺ = A_inf legitimate.
  - Discharge: openness/integral-closedness of ⊤ trivial; `isPowerBounded_Ainf`: in an
    adic ring every element is power-bounded — from `Iinf`-adic basis: x·I^n ⊆ I^n?? No:
    power-boundedness of x = boundedness of {x^k} — for adic rings: {x^k}·I^n ⊆ I^n
    since I^n is an ideal ✓ one line via `IsBounded` unfolding on the ideal basis.
  - Attacks: [1] is ⊤ ⊆ powerBounded genuinely true here (A_inf is NOT Tate!)? Yes —
    the ideal-basis argument above never needs a unit; [2] edge: the trivial ring — F
    field excludes; [3] class-shape: `IsRingOfIntegralElements` fields audit-verified
    (AffinoidRings.lean:47). SURVIVED.
- **L2.6** (internal): `Iinf_pow_two_mul_le` + **L2.7** `isHausdorff_Iinf` + **L2.8**
  `isAdicComplete_Iinf` — the completeness summit
  - Source: [Ked-AWS Def 3.1.2] (verbatim):
    > "Define the ring A_inf := W(R⁺). It is complete for the adic topology defined by
    > the inverse image of some ideal of definition of R⁺."
    plus [SW §13.1] ("(p,[p♭])-adic topology") for the presentation of that topology by
    the two-generator ideal.
  - Lean ↔ source: [Ked-AWS] presents the topology as "preimage-adic", [SW] as
    (p,[ϖ])-adic; these agree (both are the standard weak topology of A_inf), and we
    commit to the [SW] form (D4 of plan). Kedlaya's one-sentence completeness assertion
    is expanded by our own proof (source-gap rule), structured as:
    - L2.6 (leaf, elementary): I^{2n} ≤ (p)^n ⊔ ([ϖ])^n — monomial split (a+b = 2n ⟹
      a ≥ n ∨ b ≥ n). Pure `Ideal.span`/`Finset` algebra.
    - **[ROUTE REPLACED 2026-07-24 after the gpt-5.6-sol review found the original
      composition flawed (Q2 GAP: "separate p-adic + digit-wise ϖ-adic completeness ⟹
      product-filtration completeness" does not follow — J-Cauchy sequences need not be
      Cauchy in either direction separately, and Witt addition is not digit-wise; the
      old fallback `W(R) = lim_m W(R/ϖ^m)` is also non-cofinal hence insufficient).
      The binding route is now sol's two-parameter truncated-Witt argument:]**
    - L2.7a (leaf, mathlib): for perfect O_F, `A/p^r A ≅ W_r(O_F)` (truncated Witt
      vectors), because `p^r A = V^r(A)`; mathlib traction: Complete.lean's
      truncate-kernel machinery (`mem_ker_truncate`, span-p characterisations).
    - L2.7b (leaf, project): digit sandwich at each truncated level r: with
      `C_s := (ϖ^s O_F)^r` (digit-wise product filtration on W_r),
      `C_{m·p^{r-1}} ⊆ [ϖ]^m·W_r(O_F) ⊆ C_m` — via Teichmüller digit calculus
      (`[ϖ]^m·[z]·p^i = [ϖ^m z]·p^i` and the expansion machinery of
      TeichmullerSeries.lean; the general diagonal product formula is NOT in mathlib,
      per the 2026-07-24 name-verification, but the sandwich needs only the digit
      lemmas, not the general formula).
    - L2.7c (leaf, project): each `W_r(O_F)` is `[ϖ]`-adically separated and complete
      (finite product of the ϖ-adically complete O_F via L2.7b's sandwich + L1.7/L1.8).
    - L2.7d (internal): assembly:
      `A ≅ lim_r A/p^r ≅ lim_r lim_s A/(p^r + [ϖ]^s) ≅ lim_{(r,s)} A/(p^r + [ϖ]^s)
      ≅ lim_n A/(p^n + [ϖ]^n)` (double limit; the diagonal is cofinal in ℕ²), giving
      separatedness AND completeness for the product filtration J_n = (p)^n ⊔ ([ϖ])^n;
      then the sandwich L2.6 (mutual cofinality J_{2n} ≤ … ≤ J-shape with I-powers)
      transfers both to the I-adic filtration. L2.7 (`isHausdorff_Iinf`) and L2.8
      (`isAdicComplete_Iinf`) are the two public faces of L2.7d; the truncated-level
      sub-lemmas L2.7a–c enter the skeleton as named private lemmas at T204 start
      (their prose statements above are frozen; elaborating them needs
      TruncatedWittVector API iteration, deliberately deferred to the ticket).
  - Attacks (family): [1] TRAP CHECK (p,[ϖ])^n = p^n A + [ϖ]^n A? FALSE in general and
    never claimed — only the ⊔-sandwich L2.6, which is exact; [2] TRAP CHECK
    non-noetherian completion pathologies (completion not complete): avoided — we prove
    IsAdicComplete for A itself by exhibiting limits, no completion functor appears;
    [3] the "coordinates of p^n·A" claim: in W(O_F) with O_F perfect and p-torsion-free
    coefficients?? p^n·A = V^n(F^n(A))·(unit adjustments) — precise statement: for
    perfect O_F, p = V(1)·… mathlib `WittVector.Complete` proves exactly the needed
    `le_coeff_eq_iff_le_sub_coeff_eq_zero` + span-p characterisations (file read: has
    "x falls in ideal generated by p iff …" lemma around :60) — verified traction;
    [4] higher subtlety: is the product/weak topology genuinely = (p,[ϖ])-adic (RR1)?
    We never need the FULL equivalence — only the sandwich L2.6 plus the
    product-filtration completeness. VERDICT (updated 2026-07-24): the ORIGINAL
    composition (per-digit extraction) was ATTACKED SUCCESSFULLY by the external
    gpt-5.6-sol review (§0.3 Q2): coherence mod J_n does not decompose into separate
    p- and ϖ-direction Cauchy data. The route was REPLACED by the truncated-Witt
    argument (L2.7a–d above), whose composition sol supplied and endorsed. This is the
    second successful adversarial catch of the pass (after L3.3), both fixed at
    planning time.

### R1 sizing
[Ked-AWS] spends one sentence; [Bhatt Cor 3.2.3] one diagram + paragraph at the O_F
level; mathlib's p-direction file is ~200 lines. Estimate: L1.* ≈ 150–250 LOC total;
L2.1–L2.5 ≈ 150 LOC; L2.6–L2.8 ≈ 250–400 LOC (the campaign's largest single item),
anchored to the ~200-line mathlib Complete.lean as the nearest formal analogue.

---

## §2. R2 — the Frobenius φ^ℤ-action on Spa(A_inf, A_inf)

### Plain-English proof (Step 1; sources: [BFHHLWY Def 2.1.1], [SW §12.2])

O_F is perfect (L1.4), so the Witt Frobenius is a ring automorphism φ of A_inf (mathlib
`frobeniusEquiv`). φ fixes p (a natural-number cast) and sends [x] to [x^p] = [x]^p
(char p: Frobenius = map of the coefficient Frobenius, and Teichmüller is natural). φ
maps I^n into I^n (its two generators go to p and [ϖ]^p ∈ I), so φ is continuous;
φ⁻¹ sends [ϖ] to [ϖ^{1/p}] whose p-th power is [ϖ], giving I^{2n} ⊆ φ(I^n) and
continuity of φ⁻¹. Thus k ↦ φ^k is an action of ℤ by topological ring automorphisms;
functoriality of Spv/Cont/Spa under continuous ring maps (project ValuationAction) plus
stability of A⁺ = A_inf under any automorphism gives the action on Spa(A_inf, A_inf).
[SW §12.2]: "The Frobenius automorphism of O_{C♭} induces an automorphism φ of
Spa A_inf, which preserves 𝒴."

### Leaves (`FrobeniusAction.lean`)

- **L3.1** (leaf, mathlib): `frob` (def, sorry-free) + `frob_natCast`
  - Source: [BFHHLWY Def 2.1.1] ("the natural q-Frobenius", q = p).
  - Discharge: `WittVector.frobeniusEquiv p (OF F)` (needs L1.4 instance ✓);
    `map_natCast`.
  - Attacks: [1] frobeniusEquiv's underlying forward map = `WittVector.frobenius`?
    mathlib Frobenius.lean:286 defines it so (toFun := frobenius) — verified by read;
    [2] n/a; [3] n/a. SURVIVED.
- **L3.2** (leaf, mathlib): `frob_teichPi : φ([ϖ]) = [ϖ]^p`
  - Source: [SW §12.2] (κ∘φ = pκ is the log-shadow); mechanism:
    `WittVector.frobenius_eq_map_frobenius` (Frobenius.lean:273, char p) +
    `WittVector.map_teichmuller` (Teichmuller.lean:19 header) + L2.1 `teichPi_pow` at
    exponent… precisely: φ([ϖ]) = map(x↦x^p)([ϖ]) = [ϖ^p] = [ϖ]^p.
  - Attacks: [1] frobenius vs map-frobenius requires `CharP (OF F) p` ✓ L1.2;
    [2] direction: φ([ϖ]) = [ϖ]^p, NOT [ϖ^{1/p}] — φ = forward Frobenius; the INVERSE
    does the root — convention pinned here and consumed with the opposite sign by D5's
    action convention in L5.3; [3] discharge names verified by grep. SURVIVED.
- **L3.3** (leaf, project): `map_frob_Iinf_pow_le`, `Iinf_pow_two_mul_le_map_frob`,
  `continuous_frob`, `continuous_frob_symm`
  - Source: [SW §12.2] "induces an automorphism φ of Spa A_inf" presupposes topological;
    the ε-management is ours (source-gap): φ(I) ⊆ I from generators; φ⁻¹: [ϖ] =
    φ([ϖ^{1/p}]) = ([ϖ^{1/p}])^p-image ⟹ I^{2n} ⊆ φ(I^n) via monomial split (p-exponent
    untouched, [ϖ]-exponent: [ϖ]^b = φ([ϖ^{1/p}]^b) and [ϖ^{1/p}]^{2b'} ∈ … careful
    bookkeeping recorded in the ticket sketch).
  - Discharge: `Ideal.map` monotonicity + `Ideal.span` generators + continuity from
    filtration bounds via `Ideal.adicTopology` basis lemmas
    (`Ideal.hasBasis_nhds_zero_adic`-shape, AdicTopology.lean:97) +
    `continuous_of_continuousAt_zero`-shape for additive group homs (mathlib).
  - Attacks: [1] the 2n bound: is I^{2n} ⊆ φ(I^n) actually right? φ(I^n) =
    (p, [ϖ]^p)^n·(φ-image ring = whole ring since φ surjective — CAREFUL: φ(I^n) as an
    IDEAL: φ is an automorphism so φ(I^n) = ideal generated by φ-generators =
    (p, [ϖ]^p)^n. Monomials of I^{2n}: p^a[ϖ]^b, a+b = 2n. Is p^a[ϖ]^b ∈ (p,[ϖ]^p)^n
    when a ≥ n? yes (p^n divides). When b ≥ n: need [ϖ]^b ∈ ([ϖ]^p)^{?}·…: [ϖ]^b with
    b ≥ n gives ⌊b/p⌋ ≥ … NOT ENOUGH for n when p > b/… — RECOMPUTE: want p^a[ϖ]^b ∈
    (p,[ϖ]^p)^n, have a + b = 2n. If a ≥ n done. Else b > n: (p,[ϖ]^p)^n ∋ monomials
    p^i([ϖ]^p)^j, i+j = n: match i = a, j = n - a, need [ϖ]^b divisible by [ϖ]^{p(n-a)}:
    b ≥ p(n-a)? Have b = 2n - a, n > a: b - p(n-a) = 2n - a - pn + pa = n(2-p) +
    a(p-1) — for p = 2: = a ≥ 0 ✓; for p ≥ 3: n(2-p) + a(p-1) can be NEGATIVE (a
    small): e.g. p = 3, a = 0, b = 2n: need 2n ≥ 3n FALSE. **ATTACK SUCCEEDS: the
    exponent 2n is WRONG for p ≥ 3.** FIX: use I^{(p+1)n} or simply exponent p·n +
    n: monomial p^a[ϖ]^b, a + b = (p+1)n: if a ≥ n done; else b ≥ (p+1)n - n = pn ⟹
    [ϖ]^b ∈ ([ϖ]^p)^n ✓. **Corrected statement: `Iinf^((p+1)*n) ≤ map frob (Iinf^n)`.**
    Skeleton updated accordingly (see §5 changelog). This is exactly the class of error
    the adversarial pass exists to catch. Re-ran attack on corrected exponent: monomial
    split now clean for all p ✓. [2] continuity from the corrected bound: unchanged
    (any polynomial exponent works); [3] symm-continuity mirrors with roles swapped
    (φ⁻¹ fixes p, sends [ϖ] to [ϖ^{1/p}]: φ⁻¹(I^n) ⊇-bookkeeping identical). SURVIVED
    AFTER FIX.
- **L3.4** (leaf, mathlib): `instMulSemiringActionAinf` (sorry-free candidate)
  - Source: [BFHHLWY Def 2.1.1] (the group φ^ℤ).
  - Discharge: `MulSemiringAction.compHom` + `zpowersHom (RingAut _) frob` (both
    mathlib; names verified by memory of API — if `zpowersHom` has moved, fall back to
    a direct `MonoidHom` from `Multiplicative ℤ`).
  - Attacks: [1] RingAut group law composes in the right order for zpow — mathlib's
    zpowersHom is canonical; [2] smul data must be DEFINITIONALLY transparent for later
    lemmas — compHom keeps smul = (zpowersHom … g) • x reducible; an unfolding lemma
    L3.5 is stated regardless; [3] n/a. SURVIVED.
- **L3.5** (leaf, project): `ofAdd_zsmul_def`
  - unfolding lemma `k • x = (frob^k) x`; discharge: `rfl`-adjacent after L3.4's
    definitional shape; if compHom obstructs, prove by `Int.induction_on`. Attacks:
    none beyond definitional-transparency (covered in L3.4[2]). SURVIVED.
- **L3.6** (leaf, project — file edit, done): generalise
  `ValuationSpectrum.GroupAction` section by dropping the unused `[Finite G]`
  (ValuationAction.lean:39). Statement-preserving weakening; verified by inspection
  that no declaration in the section uses finiteness; policed by the build.
  - Attacks: [1] downstream users pass Finite groups — weakening cannot break them;
    [2] semantic: the definition never sums/enumerates G ✓. SURVIVED.
- **L3.7** (leaf, project): `instContinuousConstSMulAinf` + `smul_mem_spa_Ainf`
  - Source: [SW §12.2] quote above.
  - Discharge: `ContinuousConstSMul` from L3.3 continuity + zpow induction
    (`Int.induction_on`); `smul_mem_spa_Ainf` = project
    `ValuationSpectrum.smul_mem_spa` (audit: AdicSpectrum/ValuationAction, takes
    stability hypothesis — trivial for A⁺ = ⊤).
  - Attacks: [1] smul continuity for NEGATIVE k needs φ⁻¹ continuity ✓ L3.3;
    [2] Spa-stability needs CONTINUITY of the acting maps (smul_mem_cont uses
    `continuous_const_smul`) — provided by the instance being proven first — no
    circularity: instContinuousConstSMul is independent of Spa; [3] n/a. SURVIVED.

### R2 sizing
[SW] one paragraph. Estimate 120–200 LOC. (L3.3's corrected bookkeeping ≈ 60 LOC.)

---

## §3. R3 — 𝒴, the window predicates, covering / translation / disjointness

### Plain-English proof (Step 1)

**Definition of 𝒴** ([BFHHLWY Def 2.1.1]: 𝒴 = Spa(W_{E°}(F°)) \ {|p[ϖ]| = 0};
[Ked-AWS Rem. 3.1.9]: "Y_S is the subspace of v ∈ Spa(A_inf, A_inf) for which
v(p[ϖ]) ≠ 0"). In the project's vocabulary {v : ¬ v.vle (p·[ϖ]) 0} is the trace on Spa
of `basicOpen (p[ϖ]) (p[ϖ])`, hence open. φ(p[ϖ]) = p·[ϖ]^p divides (p[ϖ])^p up to the
unit-free monomial p^{p-1}: concretely v(φ(p[ϖ])) = 0 would force v(p[ϖ]) = 0 by
primality of the support — 𝒴 is φ-stable both ways.

**Element facts.** For v ∈ 𝒴 continuous: {a : v(a) < γ} is open for every nonzero value
γ, contains 0, hence contains I^N. With γ = v(p) ≠ 0: p^N ∈ I^N gives v(p)^N < v(p), so
v(p) < 1 (were v(p) ≥ 1, all powers would be ≥ 1... in a linearly ordered group γ ≥ 1
⟹ γ^N ≥ γ ≥ … contradiction chain). Likewise v([ϖ]) < 1, and for every nonzero γ some
v(p)^n < γ and v([ϖ])^n < γ (cofinality).

**The windows** ([Ked-AWS Rem. 3.1.9], verbatim):

> "Suppose that R is Tate, and let ϖ ∈ R be a pseudouniformizer. We can then make the
> description of X_S somewhat more explicit. To begin with, Y_S is the subspace of
> v ∈ Spa(A_inf, A_inf) for which v(p[ϖ]) ≠ 0. This space can be covered by the
> subspaces
>   U_n := {v ∈ Y_S : v(p)^{cp^n} ≤ v(ϖ) ≤ v(p)^{p^n}},
>   V_n := {v ∈ Y_S : v(p)^{p^{n+1}} ≤ v(ϖ) ≤ v(p)^{cp^n}}   (n ∈ Z),
> where c ∈ (1, p) ∩ Q is arbitrary. The action of φ permutes the U_n (among
> themselves) and the V_n (among themselves), and hence is properly discontinuous. The
> spaces U_0 and V_0 map isomorphically to their images in X_S and cover the latter. In
> particular, X_S can be covered by two affinoid subspaces…"

Reading (D4): "v(ϖ)" is v([ϖ]); "v(p)^{cp^n} ≤ v([ϖ])" with cp^n = a/b ∈ ℚ_{>0} means
v(p^a) ≤ v([ϖ]^b) after clearing (legitimate: multiplicativity, [ϖ]^b = [ϖ^b]). Fix
c := (p+1)/2 ∈ (1,p) ∩ ℚ (valid for every prime including p = 2: c = 3/2).

- *Covering*: for v ∈ 𝒴 write KGE q := "v([ϖ]^b) ≤ v(p^a)" (κ ≥ q), KLE q the reverse.
  Cofinality gives N with KLE(p^N) and KGE(p^{-N}) (i.e. v(p^{…}) < v([ϖ]) and
  v([ϖ]^{…}) < v(p) suitably cleared). Hence {n ∈ ℤ : KGE(p^n)} is nonempty (contains
  −N) and bounded above (fails at N+1), so has a largest element n₀; ¬KGE(p^{n₀+1}) ⟹
  KLE(p^{n₀+1}) by totality of the valuative order. Split on the middle point: KGE(c·p^{n₀})
  puts v ∈ V_{n₀}? — orientation: KGE(cp^{n₀}) ∧ KLE(p^{n₀+1}) = V_{n₀}; else
  KLE(c·p^{n₀}) ∧ KGE(p^{n₀}) = U_{n₀}. Either way v is covered.
- *Translation*: with the project convention g•v = v∘φ^{-g} (D5), (ofAdd k)•v evaluates
  [ϖ] at φ^{-k}[ϖ] = [ϖ^{p^{-k}}], so KGE q (g•v) ⟺ KGE (q/p^k) v and windows shift
  down: (ofAdd k)•U_n = U_{n-k}, likewise V.
- *Disjointness*: if v ∈ U_n ∩ U_m, n < m, then KLE(cp^n) and KGE(p^m) with
  cp^n < p^{n+1} ≤ p^m, and KLE(q') ∧ KGE(q) with q' < q is impossible on 𝒴: clearing
  to a common comparison v(p^{A}) ≤ v([ϖ]^{B}) ≤ v(p^{A'}) with A'/B > A/B ⟹
  v(p)^{AB'-ish} ≤ v(p)^{…} and the exponent-flip rule (0 < v(p) < 1) yields a false
  rational inequality. V-family: consecutive right-end cp^{n} vs left-end p^{n+1}… V_n
  windows [cp^n, p^{n+1}] and V_m, m > n: p^{n+1} ≤ cp^m needs c > p^{n+1-m}·… — the
  separation is 1 < c (strict) at m = n+1: cp^{n+1} > p^{n+1} ✓.
- *Openness*: each window = 𝒴 ∩ {two basicOpen conditions} — with the nonvanishing
  facts on 𝒴, KGE q is the basicOpen pair (v([ϖ]^b) ≤ v(p^a), v(p^a) ≠ 0) and dually,
  so windows are open in Spa.

### Leaves (`YSpace.lean`)

- **L4.1** (leaf, project): `Y` (def), `Y_subset_spa`, `Y_eq_spa_inter_basicOpen`,
  `isOpen_Y`
  - Source claim (verbatim): [BFHHLWY Def 2.1.1] "𝒴_{E,F} = Spa(W_{E°}(F°)) \
    {|p[ϖ]| = 0}"; [Ked-AWS Rem 3.1.9] "Y_S is the subspace of v ∈ Spa(A_inf, A_inf)
    for which v(p[ϖ]) ≠ 0".
  - Lean ↔ source: `{v ∈ Spa (Ainf) (ringPlus _) | ¬ v.vle (p * teichPi …) 0}` — the
    condition ¬(v(p[ϖ]) ≤ v(0)) IS v(p[ϖ]) ≠ 0 in the valuative-relation encoding
    (v(0) is the bottom). `basicOpen f f = {v(f) ≤ v(f) ∧ ¬ v(f) ≤ 0}`, and the first
    conjunct is reflexivity — exact trace equality.
  - Discharge: `basicOpen`, `isOpen_basicOpen` (RationalSubsets.lean:148),
    `spa_subtypeVal_isEmbedding` for the subspace-openness bookkeeping (pattern proven
    in the deleted legacy file's `Y_FF_isOpen`, reusable line-for-line).
  - Attacks: [1] vle-reflexivity: `v.vle f f` holds (preorder axiom of ValuativeRel) ✓;
    [2] EDGE: is 𝒴 ⊆ analytic locus (no support-open points)? v(p[ϖ]) ≠ 0 with supp
    open ⟹ I^n ⊆ supp ∋ (p[ϖ])^n ⟹ v((p[ϖ])^n) = 0 ⟹ contradiction via primality —
    recorded as a remark-level lemma if needed later, not load-bearing in this campaign;
    [3] drift: none — the two sources agree letter-for-letter with the trace reading.
    SURVIVED.
- **L4.2** (leaf, project): `Y_indep`
  - Source: [Ked-AWS §11.2] independence quote (see L2.3).
  - Discharge: divisibility ϖ'^n ∈ ϖ·O_F (as L2.3) + supp primality: v([ϖ']) ≠ 0 ⟸
    v([ϖ'^n]) ≠ 0 ⟸ v([ϖ]·u) ≠ 0-chains.
  - Attacks: [1] both directions needed — symmetric ✓; [2] n/a; [3] the quote concerns
    the locus {[ϖ] ≠ 0} not {p[ϖ] ≠ 0} — same argument applies to the product since the
    p-factor is choice-independent; gloss recorded. SURVIVED.
- **L4.3** (leaf, project): `smul_mem_Y`
  - Source: [SW §12.2] "which preserves 𝒴".
  - Discharge: L3.2 + supp primality: v(φ^{-k}(p[ϖ])) = v(p·[ϖ^{p^{-k}}]) ≠ 0 ⟸
    v(p) ≠ 0 ∧ v([ϖ^{p^{-k}}]) ≠ 0, and v([ϖ^{p^{-k}}])^{p^k} = v([ϖ]) via L2.1.
  - Attacks: [1] both signs of k ✓ symmetric; [2] needs product-splitting
    v(ab) ≠ 0 ⟺ v(a) ≠ 0 ∧ v(b) ≠ 0 — supp is prime (mathlib ValuativeRel/project
    `supp` API, audit-verified `supp` exists with prime instance — verify name at
    fill); [3] n/a. SURVIVED.
- **L4.4** (leaf, project): `v_p_ne_zero`, `v_teichPi_ne_zero`, `vlt_p_one`,
  `vlt_teichPi_one`
  - Source: continuity manipulation — our expansion (source-gap; the sources treat κ's
    well-definedness on 𝒴 as read, [SW §12.2]).
  - Discharge: continuity definition (`Valuation.IsContinuous`,
    ContinuousValuations.lean:34: ∀ γ, IsOpen {a | v a < γ}) + `Iinf`-basis
    (`Ideal.hasBasis_nhds_zero`) + linear-order chains in the value group via the
    `ValuativeRel.valuation` bridge (project `ofValuation`-family, audit-verified).
  - Attacks: [1] the strictness derivation v(p)^N < v(p) ⟹ v(p) < 1: in a linearly
    ordered group with γ ≠ 0: if γ ≥ 1 then γ^N ≥ γ (induction, needs N ≥ 1: N = 0
    edge gives v(1) < v(p) ≤ 1 — also fine, contradiction differently; case handled);
    [2] TRAP: {a | v a < γ} for γ = v(p) requires v(p) as a VALUE-GROUP element —
    the project's IsContinuous quantifies over Γ; instantiating needs the
    element-to-value bridge — mechanical via `ValuativeRel.valuation v p`; [3] trivial
    valuation: v trivial with v(p[ϖ]) = 1 would need {v < 1} = supp open — 𝒴 avoids it
    exactly by this argument; no extra hypothesis needed. SURVIVED.
- **L4.5** (leaf, project): `exists_pow_p_vlt`, `exists_pow_teichPi_vlt` (cofinality)
  - Source: as L4.4 (continuity, our expansion; implicit in [Ked-AWS Rem 3.1.9]'s
    covering claim).
  - Discharge: same continuity route with γ = v(g).
  - Attacks: [1] g arbitrary with v(g) ≠ 0 — quantifier order fine; [2] n ≥ 1 vs n = 0:
    p^0 = 1, v(1) < v(g) possible only if v(g) > 1 — FALSE on Spa (v ≤ 1 everywhere,
    A⁺ = ⊤)! So conclusions must allow n ≥ 1 — statement says ∃ n, fine (n = 0 never
    forced); noted for the prover; [3] IMPORTANT: v(g) ≤ 1 is imposed by A⁺ = A_inf
    membership (Spa def) — NOT automatic for continuous valuations on non-Tate rings;
    our Spa-based 𝒴 has it by definition — consistency between sources' Spa(A_inf,
    A_inf) and ours confirmed (all sources use the self-pair). SURVIVED.
- **L4.6** (leaf, project): `KGE`/`KLE` (defs) + `KGE_iff`/`KLE_iff`
  (representation-independence) + `KGE_or_KLE` (totality) +
  `not_KGE_of_KLE_of_lt` (order-incompatibility)
  - Source: [Ked-AWS Rem 3.1.9] inequalities + D4 clearing gloss; [SW §12.2] κ.
  - Lean ↔ source: KGE (a/b) v := v.vle ([ϖ]^b) (p^a) renders v(p)^{a/b} ≥ v([ϖ]) i.e.
    κ(v) ≥ a/b. Note the DIRECTION: bigger κ ⟺ [ϖ] smaller relative to p — matches
    [SW §12.2] κ(x_{C♭}) = 0 (p-vanishing end has κ = 0: there v(p) = 0… consistency
    spot-check: at κ→∞ end [p♭] = 0 [SW Fig 12.1 x_L axis "[p♭] = 0"] ⟹ v([ϖ]) = 0 ⟺
    KGE q for ALL q ⟺ κ = ∞ ✓ orientation confirmed against the figure).
  - Discharge: cross-multiplication inside the value monoid via `vle`-calculus
    (mul-compat axioms of ValuativeRel), `Rat.num/den` arithmetic (`Rat.num_div_den`,
    positivity), exponent-flip: δ^a ≤ δ^b ⟹ a ≥ b for δ < 1 — a small ordered-monoid
    lemma likely NOT in mathlib in vle form: planned as a private helper on
    `ValuativeRel.valuation` values (`pow_le_pow_iff_right_of_lt_one`-shape DOES exist
    in mathlib for ordered semirings/groups — `pow_le_pow_iff_right_of_lt_one` /
    `one_lt_pow_iff`-family; verify against `LinearOrderedCommGroupWithZero` instances
    at fill).
  - Attacks: [1] q ≤ 0 degenerate: definitions use `q.num.toNat` — junk-value semantics
    documented; every consumer passes 0 < q; [2] normalisation: ℚ is always
    reduced in mathlib, and `KGE_iff` handles arbitrary representations — the iff needs
    v(p) < 1?? NO wait: representation-independence v([ϖ]^{b}) ≤ v(p^{a}) ⟺
    v([ϖ]^{b'}) ≤ v(p^{a'}) for a/b = a'/b' needs raising both sides to powers b', b —
    uses ONLY multiplicativity + order-compat + CANCELLATION: γ^k ≤ δ^k ⟹ γ ≤ δ —
    true in linearly ordered groups-with-zero (k ≥ 1) via strict-mono of pow — fine
    without v(p) < 1; hypothesis (hv : v ∈ Y) kept anyway for the nonvanishing corner
    (0-cases of γ,δ) — re-examined: if v(p) = 0 the flip/cancellation arguments have
    0-edge-cases; keeping hv is the safe, honest signature ✓; [3] totality: ValuativeRel
    order is total on values (axiom) ✓; [4] `not_KGE_of_KLE_of_lt` recomputed
    independently in §3 prose (disjointness) ✓ consistent. SURVIVED.
- **L5.1** (leaf, project): `cFF`, `one_lt_cFF`, `cFF_lt_p`
  - Source: [Ked-AWS Rem 3.1.9] "c ∈ (1,p) ∩ Q is arbitrary" — we fix c = (p+1)/2.
  - Attacks: [1] p = 2: c = 3/2 ∈ (1,2) ✓; p = 3: 2 ∈ (1,3) ✓; general: 1 < (p+1)/2 ⟺
    p > 1 ✓; (p+1)/2 < p ⟺ p > 1 ✓; [2] "arbitrary" hides nothing: c only enters via
    1 < c < p in disjointness and the U/V-interface — fixing it loses no theorem in this
    campaign (the charts change, the curve does not); [3] rational-arithmetic
    discharge: `norm_num`-level. SURVIVED.
- **L5.2** (leaf, project): `windowU`, `windowV` (defs) + `isOpen_windowU/V`
  - Source: [Ked-AWS Rem 3.1.9] verbatim (above).
  - Lean ↔ source: windowU n = {v ∈ Y | KGE(p^n) ∧ KLE(c·p^n)} — matches U_n exactly
    under D4/D5 readings; openness via the basicOpen decomposition of each cleared
    inequality plus the nonvanishing facts L4.4 (the ≠0 side-conditions of `basicOpen`
    hold automatically on 𝒴).
  - Attacks: [1] zpow of ℚ at negative n: `(p:ℚ)^n` for n : ℤ is `zpow` ✓ positive ✓;
    num/den extraction of c·p^n: via `KGE_iff` any representation works — the DEFS use
    the normalised form, the PROOFS use the iff — no fragility; [2] windows ⊆ 𝒴 by
    definition ✓; [3] openness: intersection of TWO basicOpens + open 𝒴 ✓ finite ✓.
    SURVIVED.
- **L5.3** (leaf, project): `zsmul_windowU`, `zsmul_windowV` (translation)
  - Source: [Ked-AWS Rem 3.1.9] "The action of φ permutes the U_n (among themselves)
    and the V_n (among themselves)"; [SW §12.2] "φ sends 𝒴_{[a,b]} isomorphically to
    𝒴_{[ap,bp]}".
  - Lean ↔ source: our g•v = v∘φ^{-g} (D5) makes the shift n ↦ n - k; SW's pushforward
    makes it up — same orbit partition. The set-level equality with `Set.smul_set` is
    the cleanest transport form for the quotient arguments.
  - Discharge: L3.2/L3.5 + `KGE`-transformation lemma: KGE q (g•v) ⟺ KGE (q·p^{-k}) v —
    via [ϖ]-evaluation: (g•v)([ϖ]^b) = v(φ^{-k}([ϖ])^b) = v([ϖ^{p^{-k}}]^b) and
    ([ϖ^{p^{-k}}])^{b·p^k} = [ϖ]^b — clearing p^k into the rational index. Careful
    ℚ-arithmetic: (p^n)·p^{-k} = p^{n-k} ✓ zpow_add.
  - Attacks: [1] SIGN recomputed twice (here and D5) — consistent; the skeleton
    statement `= windowU (n - k)` matches; [2] set-image vs preimage: `g • S` as
    pointwise image; equality (not just ⊆) needs both directions — action by bijections
    ✓; [3] q·p^{-k} positivity ✓. SURVIVED.
- **L5.4** (leaf, project): `windowU_disjoint`, `windowV_disjoint`
  - Source: [Ked-AWS Rem 3.1.9] (implicit in "hence is properly discontinuous"; the
    interval arithmetic is ours per D4).
  - Discharge: `not_KGE_of_KLE_of_lt` (L4.6) + rational inequalities cp^n < p^{n+1}
    (c < p) and p^{n+1} < cp^{n+1} (1 < c) — `norm_num`/`gcongr`-level with zpow.
  - Attacks: [1] U-U at distance 1 recomputed: U_n right end cp^n < U_{n+1} left end
    p^{n+1} ⟺ c < p ✓ STRICT; V-V: V_n right end p^{n+1} < V_{n+1} left end cp^{n+1}
    ⟺ 1 < c ✓ STRICT; [2] U_n ∩ V_n ≠ ∅ is EXPECTED (shared boundary cp^n) — only
    within-family disjointness claimed, and the quotient argument only uses
    within-family ✓ (Kedlaya's "permutes the U_n among themselves" line is exactly
    this); [3] boundary points κ = exactly cp^n live in both U_n and V_n — harmless.
    SURVIVED.
- **L5.5** (leaf, project): `Y_eq_iUnion_windows` (covering)
  - Source: [Ked-AWS Rem 3.1.9] "This space can be covered by the subspaces U_n … V_n".
  - Discharge: L4.5 (both cofinalities, cleared into KLE(p^N)/KGE(p^{-N})), classical
    largest-element extraction on the finite range {-N, …, N} (Int induction /
    `Finset.max'`), totality L4.6, split on c·p^{n₀}.
  - Attacks: [1] existence of the largest n with KGE(p^n): the set is nonempty
    (KGE(p^{-N}) from clearing v([ϖ]^{…}) < v(p): CHECK the clearing — v([ϖ])^M < v(p)
    ⟹ KGE(1/M) ⟹ KGE(p^{-N}) for p^{-N} ≤ 1/M by monotonicity — needs KGE.mono
    (downward monotone in q) — INCLUDED in L4.6's iff/mono family; bounded above (else
    KGE(p^m) ∀m ⟹ v([ϖ]^{…}) ≤ v(p^{…}) contradicting KLE(p^N) + incompatibility
    L4.6) ✓ so `Int` interval finite, max exists classically ✓; [2] HIGHER-RANK CHECK
    (the adversarial question): the argument never compares v([ϖ]) to real numbers —
    only finitely many vle-facts + totality — rank-free ✓ no Archimedean assumption
    smuggled: the "κ ∈ [p^{-N}, p^N]" is shorthand for two vle-facts, and the max is
    over INTEGERS, not group elements ✓; [3] n₀ vs n₀+1 fencepost recomputed in §3
    prose ✓. SURVIVED.

### R3 sizing
[Ked-AWS Rem 3.1.9] is 10 lines of source for the full window system; our expansion
(clearing + rank-free order theory) is the campaign's second-largest item. Estimate:
L4.* ≈ 200–300 LOC; L5.* ≈ 250–350 LOC.

---

## §4. R4–R5 — freeness, wandering, and the curve 𝒳

### Plain-English proof (Step 1)

**Freeness** (corollary route — no independent value-group argument): let v ∈ 𝒴 with
φ^k·v = v, k ≠ 0. By covering, v ∈ U_n (or V_n) for some n; by translation
φ^k·v ∈ U_{n-k} (resp. V_{n-k}); so v ∈ U_n ∩ U_{n-k} = ∅ (within-family disjointness,
k ≠ 0). Contradiction. **Wandering**: v's own window W is an open neighbourhood inside
𝒴, and φ^k·W ∩ W = ∅ for k ≠ 0 (translation + disjointness). This is the precise
content behind [Ked-AWS §3.1] "The action of φ on Y_S is properly discontinuous" and
[SW Def 13.5.1] "As φ acts properly discontinuously on 𝒴_(0,∞) (as follows from
κ∘φ = pκ), it makes sense to form the quotient."

**The curve** ([BFHHLWY Def 2.1.1]: 𝒳 = 𝒴/φ^ℤ): the orbit-relation quotient of the
subtype ↥𝒴, with the quotient topology. The quotient map is an open quotient map
(mathlib: orbit maps of continuous actions). On each window it is injective: two window
points in one orbit contradict wandering. Hence each window maps homeomorphically onto
an open subset ([Ked-AWS Rem 3.1.9]: "The spaces U_0 and V_0 map isomorphically to
their images in X_S"), and the images of U_0, V_0 cover 𝒳 ("and cover the latter"):
every orbit meets U_0 ∪ V_0 by covering + translation (shift the witnessing window
index to 0). T0: orbits are separated because distinct orbits either differ inside one
window-chart (T0 there, inherited from Spv) or lie over different κ-data; formally: the
quotient of a T0 space by an open equivalence relation with discrete-fibre-like
(wandering) structure is T0 — proven via the chart embeddings. Quasicompactness: 𝒳 =
q(U_0) ∪ q(V_0) with each q(U_i) a continuous image of the quasicompact window-closure
data ([Ked-AWS Rem 3.1.9]: "In particular, X_S can be covered by two affinoid
subspaces"); in our layer, window quasicompactness comes from the project's Boolean
product-embedding compactness machinery (SpaCompact/ValuationSpectrumCompact: Spa is
compact; the window adds finitely many coordinate conditions — two vle-closed and two
clopen-style nonvanishing — the resulting subset is compact by the closed-image
criterion `isCompact_spa_of_isClosed_image`-family).

### Leaves (`Curve.lean`)

- **L6.1** (leaf, project): `smul_ne_of_ne_zero` (freeness)
  - Source: [Ked-AWS Rem 3.1.9]/[SW Def 13.5.1] as quoted; the corollary-route is our
    arrangement (gloss recorded; mathematically it is exactly "φ permutes the U_n among
    themselves ⟹ properly discontinuous ⟹ free on the covered set").
  - Discharge: L5.5 + L5.3 + L5.4, pure set logic.
  - Attacks: [1] k < 0 handled by symmetry (n - k ≠ n ⟺ k ≠ 0 for both signs) ✓;
    [2] boundary points in U_n ∩ V_n: the argument uses whichever family contains v —
    both work ✓; [3] no hidden use of Hausdorffness ✓. SURVIVED.
- **L6.2** (leaf, project): `exists_nhd_smul_disjoint` (wandering)
  - Source: as L6.1.
  - Discharge: L5.2 (openness) + L5.3 + L5.4; the existential witnesses v's window.
  - Attacks: [1] the neighbourhood must be a subset of 𝒴 ✓ windows are; [2] `Set.smul`
    disjointness vs pointwise: `Disjoint (g • W) W` unfolds pointwise ✓; [3] the
    "for all k ≠ 0 simultaneously" is exactly within-family disjointness at all
    distances ✓. SURVIVED.
- **L6.3** (leaf, project): `instMulActionYSub` (data real, laws one-line) +
  `instContinuousConstSMulYSub`
  - Discharge: pattern of project `instMulActionCont` (ValuationAction.lean:71) —
    Subtype.ext + parent laws; continuity: restriction of continuous maps to
    subtypes (`Continuous.subtype_mk` + `continuous_subtype_val` composition), from
    L3.7 through the Spv-level action.
  - Attacks: [1] CAREFUL: the Spv-level continuity of g•(-) — comap-continuity is
    project `comap_continuous` (audit-verified, ValuationSpectrum.lean:107) — the
    ContinuousConstSMul on Spv-subsets follows; the subtle point is which topology ↥𝒴
    carries (subspace of Spv ✓ unambiguous); [2] n/a; [3] n/a. SURVIVED.
- **L7.1** (leaf, mathlib): `Curve` (def), `toCurve`, `toCurve_surjective`,
  `isOpenQuotientMap_toCurve`
  - Source (verbatim): [BFHHLWY Def 2.1.1] "𝒳_{E,F} = 𝒴_{E,F}/φ^**Z**"; [SW Def
    13.5.1] "The adic Fargues-Fontaine curve is the quotient 𝒳_FF = 𝒴_(0,∞)/φ^**Z**."
  - Lean ↔ source: `Quotient (MulAction.orbitRel (Multiplicative ℤ) ↥Y)` with the
    quotient topology is the literal 𝒴/φ^ℤ as a topological space; the adic-structure
    layer is D3-deferred (the sources' own Prop 2.1.2 delegation).
  - Discharge: `Quotient.mk_surjective`;
    `MulAction.isOpenQuotientMap_quotientMk` (mathlib, ConstMulAction.lean:574, needs
    `[ContinuousConstSMul]` = L6.3).
  - Attacks: [1] orbitRel vs "∃ k, φ^k x = y": definitional match of `MulAction.orbitRel`
    ✓; [2] which quotient topology: `instTopologicalSpaceQuotient` = coinduced ✓ the
    open-quotient-map theorem is against exactly this instance ✓; [3] n/a. SURVIVED.
- **L7.2** (leaf, project): `injOn_toCurve_windowU/V`
  - Source: [Ked-AWS Rem 3.1.9] "map isomorphically to their images".
  - Discharge: wandering L6.2 specialised to window-mates: if q(x) = q(y), x = φ^k·y;
    if both in U_n and k ≠ 0 then x ∈ U_n ∩ U_{n-k} = ∅ — so k = 0.
  - Attacks: [1] the InjOn set lives in ↥𝒴 with a coercion to Spv — statement uses the
    coercion consistently ✓; [2] n/a; [3] n/a. SURVIVED.
- **L7.3** (leaf, project): `curve_eq_image_window_zero`
  - Source: [Ked-AWS Rem 3.1.9] "U_0 and V_0 … cover the latter".
  - Discharge: covering L5.5 + translation L5.3: v ∈ U_n ⟹ (ofAdd n)•v ∈ U_0 with the
    same orbit ⟹ q(v) ∈ q(U_0).
  - Attacks: [1] sign of the shift: v ∈ U_n, want image in U_0 = U_{n - n} ⟹ act by
    ofAdd n ✓ (D5 convention: shifts DOWN by k) ✓ recomputed; [2] n/a; [3] n/a.
    SURVIVED.
- **L7.4** (leaf, project): `instT0SpaceCurve`
  - Source: implicit in the sources treating 𝒳 as an adic space (adic spaces are T0);
    our proof is chart-wise (gloss: no source proves T0 separately — it follows from
    their sheaf-level structure; at our layer the chart embeddings + Spv's T0 give it;
    this is an honest ADDITION, low risk).
  - Discharge: L7.1 (open quotient) + L7.2 (chart injectivity) + T0 of Spv (project:
    Spv points are extensionally the relations — T0 via `basicOpen` separation;
    verify the project's exact T0 lemma for Spa-subspaces at fill time; if missing, a
    small sub-leaf: distinct valuative relations are separated by a `basicOpen`, which
    is essentially `Spv.ext` + definition of the topology).
  - Attacks: [1] two points in ONE chart: separated by chart-open sets ✓; two points
    with disjoint κ-windows: preimages saturate to disjoint unions of translated
    windows?? — careful: T0 needs only SOME open containing one not the other; the
    image of the window of x is open (L7.1+L7.2) and misses y's orbit unless y's orbit
    meets x's window — in which case reduce to the one-chart case ✓ argument closes;
    [2] no Hausdorff claim is made (𝒳 is NOT Hausdorff — adic spectra aren't; only T0)
    ✓ scope-correct; [3] n/a. SURVIVED.
- **L7.5** (leaf, project): `isCompact_windowU_zero`, `isCompact_windowV_zero`,
  `instCompactSpaceCurve`
  - Source: [Ked-AWS Rem 3.1.9] "In particular, X_S can be covered by two affinoid
    subspaces" (affinoid ⟹ quasicompact; our layer proves the quasicompactness
    directly).
  - Discharge: project Boolean-embedding compactness machinery
    (`isCompact_spa_of_isClosed_image` criterion family, SpaCompact.lean:47) — the
    window adds four coordinate conditions to the closed image; each `{v : v.vle a b}`
    is a closed coordinate condition and each nonvanishing `{¬ v.vle s 0}` is also a
    coordinate condition (the Boolean-product trick handles arbitrary Boolean
    combinations of FINITELY many vle-coordinates, since a clopen modification of a
    closed set within a compact product stays closed when the conditions are
    coordinate-determined — TO VERIFY against the project's exact criterion; if the
    criterion only handles closed conditions, fall back to spectral-space style:
    window = intersection of a closed set with two quasicompact basicOpens, and
    finite intersections of qc opens in a spectral-like space are qc — the project's
    SpaQCviaSpvAI may already provide the needed "qc basicOpen" statement).
    **Honesty flag: this is the least-pinned discharge of the campaign** — compactness
    of rational-style subsets is morally in the project's wheelhouse (SpaCompact,
    SpaQCviaSpvAI) but the exact citable lemma was not located during planning; the
    ticket carries both candidate routes and a hard-stop instruction if neither lands
    (downgrade `instCompactSpaceCurve` to a stated-not-proved stretch WITHOUT changing
    any other statement — it is a leaf with no dependents in this campaign).
  - Attacks: [1] window is NOT closed in Spa (nonvanishing is open-ish in the spectral
    sense) — the discharge routes above are chosen precisely to avoid "closed subset of
    compact" naivety; [2] CompactSpace of the quotient: continuous image of
    qc ∪ qc ✓ via L7.3 + `IsCompact.image` + `isCompact_union`; [3] the sources' word
    "affinoid" is STRONGER than qc — we claim only qc ✓ under-claiming is safe.
    SURVIVED (with the honesty flag).
- **L7.6** (leaf, STRETCH, project): `Y_nonempty`
  - Source: [FF §1.4]-family (multiplicative Gauss norms |·|_ρ on A_inf) — reserved;
    not decomposed in this campaign beyond the statement. Explicitly ticketed as
    stretch with its own future sub-decomposition; NO other leaf depends on it.
  - Attacks: [1] the statement is true for every perfectoid F (Gauss norms exist in
    complete generality — [FF] work over any perfectoid F, alg. closedness enters
    later), so the skeleton statement is safe to keep; [2] risk isolated: no dependent
    ✓; [3] n/a. SURVIVED (as a stretch marker).

### R4–R5 sizing
[Ked-AWS §3.1 + Rem 3.1.9]: ~15 lines of source. Estimate: L6.* ≈ 80–140 LOC; L7.1–7.4
≈ 150–250 LOC; L7.5 ≈ 100–200 LOC (or descoped); L7.6 stretch unbounded (own future
campaign section).

---

## §5. Takeover verdict on pre-existing files (audit 2026-07-24)

- **`Adic spaces/FarguesFontaine.lean` (legacy, DELETED by this campaign).** Verdict
  from the read + audit: (i) its `Y_FF` removed the SIMULTANEOUS vanishing locus
  V(p,[π]) = {v(p) = 0 ∧ v([π]) = 0}, not the paper's V(p·[ϖ]) = {v(p[ϖ]) = 0} — the
  quotient of that space by φ^ℤ is NOT the Fargues–Fontaine curve (Frobenius fixes the
  char-p locus V(p) pointwise: v∘φ = v^p there, an equivalent valuation, so the action
  on the extra locus is trivial and the quotient is not even T0-reasonable there);
  (ii) its Witt topology instance was p-adic (`span {p}`), not (p,[ϖ])-adic — the wrong
  Spa; (iii) its four "key property" theorems were vacuous (`∀ _, True`); (iv) 10 code
  sorries including a sorry'd `Setoid` DATA instance. Nothing mathematically load-
  bearing was lost; the two reusable idioms (the `teichmullerPi` construction and the
  basicOpen-union openness proof pattern) were carried into `PseudoUniformizer.toOF` /
  `isOpen_Y`'s planned proof. History remains in git.
- **Kept and consumed as-is:** PseudoUniformizer.lean, PerfectoidRing.lean (classes +
  the p-adic completeness engine), WittVectorPrimitive.lean (future untilt campaigns),
  Tilting.lean (future: F = C♭ instances for L7.6 route (ii)).
- **Edited:** ValuationAction.lean (L3.6, `[Finite G]` dropped); root
  `Adic spaces.lean` import swap (legacy → five new modules).
- **Skeleton changelog during the pass:** (a) `OF`/`toOF` signatures corrected (variable
  capture: `p` is not a parameter of either); (b) ϖ-parametrised completeness
  statements demoted from `instance` to `theorem` (unsynthesisable parameter);
  (c) **L3.3's φ⁻¹-continuity bound corrected from `I^{2n} ⊆ φ(I^n)` to
  `I^{(p+1)n} ⊆ φ(I^n)`** — caught by the adversarial pass (attack log at L3.3), the
  2n-bound is false for p ≥ 3.

## §6. Residual-risk register (what the confidence gate could NOT fully close)

- **RR1 (completeness fine structure) — RESOLVED 2026-07-24.** The external review
  (§0.3 Q2) confirmed the risk was real: the coefficientwise expansion had a genuine
  gap, and the old fallback (lim_m W(O_F/ϖ^m)) was itself non-cofinal. Both replaced
  by the validated truncated-Witt route (L2.7a–d), which needs no noetherian input and
  has direct mathlib traction at each step. Residual exposure is now ordinary
  formalisation effort, not route risk.
- **RR2 (window-compactness discharge, L7.5).** Two candidate routes named; hard-stop +
  descope instruction embedded in the ticket; no dependents.
- **RR3 (external review) — RESOLVED 2026-07-24.** Delivered (§0.3); verdicts
  integrated. The review confirmed the window machinery outright (Q1/Q4/Q6/Q7),
  repaired the completeness route (Q2 → L2.7a–d), and supplied the Q5 explicitness
  checklist now embedded in the tickets. Reply archived verbatim:
  `chatgpt-reply-fargues-fontaine-2026-07-24.md`.

## §7. Confidence-gate summary (Step 5)

1. Every leaf discharged from mathlib/project or explicitly sub-planned: ✓ (L7.6
   stretch-marked, no dependents; RR1/RR2 carry named fallback routes).
2. Skeleton compiles, sorries only: ✓ **GREEN 2026-07-24** (full-library build; §0.5).
3. Verbatim source quote per leaf-family + Lean↔source paragraphs: ✓ (grouped where
   the mathematics is shared; every group carries its quote).
4. Adversarial pass with ≥3 attack categories per leaf-family, all outcomes recorded:
   ✓ — one successful attack (L3.3) found and FIXED during the pass.
5. Prior-B2 consultation: ✓ (§0.4, clean).
6. Tree mirrors the sources' structure ([BFHHLWY Def 2.1.1] for the statements,
   [Ked-AWS 3.1.2/3.1.5/3.1.9] for the construction, expansions marked as ours per the
   source-gap rule); LOC estimates anchored to source line counts per §-sizing blocks.
7. Single-conclusion statements throughout (no ∧-bundles; window pair-lemmas split
   U/V; assembly nodes absent by design).
