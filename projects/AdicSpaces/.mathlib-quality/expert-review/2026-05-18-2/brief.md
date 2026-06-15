# Review brief — Tate acyclicity sorry inventory: comprehensive accuracy + cascade audit

*Prepared 2026-05-18 (Session 22 follow-up) for the same mathematical-model reviewer who answered the 2026-05-18 brief in `expert-review/2026-05-18/brief.md`. Self-contained; no repo access required.*

*This is a **comprehensive per-leaf audit**: we want a reviewer verdict on the accuracy AND cascade-survivability of every single `sorry` in the IsSheafy transitive dependency closure (~52 leaves). The prior brief asked about ~5 directly-suspect leaves; this one asks about all 52. The cascade question is new and triggered by an oversight in the prior brief — see §1.2.*

---

## 1. Goal of this brief

### 1.1. Project goal (unchanged from prior brief)

Formalise Wedhorn Theorem 8.28(b) in Lean 4 on Mathlib: for an affinoid ring $(A, A^{+})$ with $A$ a strongly noetherian Tate ring, the presheaf $\mathcal{O}_X$ on $X = \mathrm{Spa}(A, A^{+})$ is a sheaf of complete topological rings. The current Lean target captures the sheaf-of-sets half (existence + uniqueness of glueings + topological embedding), packaged as a typeclass `IsSheafy`. Higher Čech cohomology vanishing is scoped out.

### 1.2. Brief goal — accuracy + cascade per leaf

Two questions for each in-scope `sorry`-bodied leaf $L$:

- **Accuracy.** Is $L$'s statement (the type signature in the project) actually true under the stated hypothesis profile?
- **Cascade-survivability.** Is $L$'s currently-attempted proof route blocked by (a) a deletion we made since the prior brief, (b) an open problem in the literature, or (c) a hypothesis weaker than the proof actually needs? If yes, can the statement be salvaged by a different route, or should it be deleted/restated?

**Why the brief is structured this way.** The prior brief asked only about a few directly-suspect leaves (B2/B3/B4, F2/F3) and got reviewer confirmation that they were false. We deleted those. But several remaining leaves — ones the prior brief marked ✓ — turn out on second audit to depend (in their proof route, not their statement) on the deleted lemmas. We should have asked the cascade question then; we are asking it now. We want to avoid a third round where we discover more "✓-marked-but-actually-load-bearing-on-something-now-deleted" leaves.

### 1.3. State changes since the prior brief

The prior brief (2026-05-18) was answered with the reply summarised in §1.4. Following that reply, we performed two further passes:

- **Session 21 (hard deletion)**: deleted nine declarations the reviewer flagged as load-bearing on false content — `isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate`, `isNoetherianRing_A₀_of_stronglyNoetherianTate`, `isStronglyNoetherian_of_isNoetherianRing_isTateRing` (B2/B3/B4), `restrictionMapHom_surj`, `restrictionMapHom_injective` (G1/G2), `restrictionMap_isLocalization` (the false Prop 8.15 IsLocalization claim), and three "Wedhorn-clean" Lemma 8.31 wrappers (L1/L2/L3) plus one cascade consumer.

- **Session 22 (`/develop --decompose` second pass)**: re-audited every remaining in-scope `sorry`. Found four additional accuracy concerns, all flagged in the catalog below (A3, B5, F5, I2).

The current state: $\sim 52$ `sorry`-bodied leaves in the IsSheafy transitive dependency closure (down from $\sim 55$); `lake build` clean; six leaves closed entirely (Cluster D items D3, D4, D11, D13, D15, D16 — Wedhorn 7.40(5) sub-step, Wedhorn 7.51 part 1, Wedhorn 7.51 sub-step on $A^{\times}$ openness, and Wedhorn 7.52(2)).

### 1.4. Reviewer's prior verdict (anchor for this brief)

The previous reply established:

1. Strongly noetherian Tate does not imply noetherian ring of definition (the $\mathbb{C}_p$ counterexample). Do not route Wedhorn 8.28(b) through such a derivation.
2. Noetherian Tate does not imply strongly noetherian Tate in known generality. Keep `[IsStronglyNoetherian A]` explicit.
3. Wedhorn 7.54 / standard-cover refinement at a rational base must be relativised over $\mathcal{O}_X(C_{\mathrm{base}})$, not stated over $A$.
4. Keep the Wedhorn architecture; remove the false wrappers; make parametric variants explicit.
5. `IsSheafy` at the sheaf-of-sets level does not need full Čech cohomology — Cor 8.32 separation plus degree-zero Laurent gluing plus refinement transfer suffices.

We adopted all five recommendations. The recommended clean route is:

$$[\mathrm{IsStronglyNoetherian}\,A] \xrightarrow{\text{Ex 6.38}} \text{rational localizations preserved} \xrightarrow{\text{Prop 8.30}} \text{flat restrictions} \xrightarrow{\text{Cor 8.32}} \text{faithfully flat product} \xrightarrow{\text{Lem 8.34 } H^0} \text{IsSheafy}.$$

This brief is now a leaf-by-leaf check that each step of this clean route corresponds to an in-scope `sorry` with an accurate statement and a discharge route the reviewer agrees is feasible.

---

## 2. Background and references

### 2.1. Setting (compact — same as prior brief)

Commutative rings with $1$. **$f$-adic ring** = topological ring with an open subring of definition $A_0$ which is $I$-adic for a finitely generated ideal $I$; pair $(A_0, I)$ is a **pair of definition**. **Tate ring** = $f$-adic with a topologically nilpotent unit. $A^{\circ}$ = power-bounded elements, $A^{\circ\circ}$ = topologically nilpotent elements. **Ring of integral elements** $A^{+}$ = integrally closed open subring with $A^{\circ\circ} \subseteq A^{+} \subseteq A^{\circ}$. **Affinoid ring** = pair $(A, A^{+})$. **Spa** = $\{v \in \mathrm{Cont}(A) : v(f) \le 1\,\forall f \in A^{+}\}$. **Rational subset** $R(T/s) = \{v \in \mathrm{Spa}\,A : v(t) \le v(s) \ne 0\,\forall t \in T\}$ for $T$ finite with $T \cdot A$ open and $s \in A$. $\mathcal{O}_X(R(T/s)) = A\langle T/s \rangle$ = completion of $A_s = A[s^{-1}]$ in the unique non-arch topology making $\{t/s\}$ power-bounded. **Strongly noetherian Tate** = $A\langle X_1, \dots, X_n \rangle$ noetherian for every $n$.

### 2.2. References

- **[Wedhorn]** Torsten Wedhorn. *Adic Spaces*. arXiv:1910.05934v1, 2019.
- **[Hu1, Hu2, Hu3]** R. Huber's three papers on continuous valuations / formal-rigid varieties / étale cohomology of adic spaces.
- **[BGR]** Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*, Grundlehren 261, 1984. (§5.2.6 Theorem 1: completely valued height-1 fields are strongly noetherian Tate.)
- **[Stacks]** Stacks Project. Tags `023N` (faithfully flat descent), `0316` (= Lemma 10.97.6: $I$-adic completion of noetherian is noetherian — corrected from prior brief's incorrect `00MA`).
- **[Hübner]** K. Hübner, *Sheafiness of Huber's valuation spectrum*, arXiv:2405.06435.

### 2.3. State of the art

Wedhorn 8.28(b) is established mathematically (Huber 1994, BGR 5.2.6 chain). To our knowledge, this Lean development is the first attempt at the full theorem. The known proofs all route through either (a) Wedhorn 6.18-style noetherianity of a ring of definition, or (b) the BGR chain for completely valued fields. Strategy (a) is not available in the project's current setting (per the prior reviewer's Q1 answer). Strategy (b) is restrictive. **A genuinely strong-noetherian-only proof of 8.28(b) for fully general $A$ is unclear** — this is one of the focal questions of this brief (Q-META.1).

---

## 3. Strategy (post-Session-21 clean route)

```
[IsStronglyNoetherian A]
   → Example 6.38 (rational localizations of strongly noeth Tate are strongly noeth Tate)
   → Prop 8.30 (rational restriction maps are flat)
   → Cor 8.32 (product restriction is faithfully flat)
   → degree-zero Laurent exactness (Lemma 8.33 + 8.34 H^0 content)
   → IsSheafy (sheaf-of-sets level)
```

The chain is implemented as named sorries in the catalog below. The catalog also surfaces what we previously called "Cluster D" (the Wedhorn 7.40–7.52 chain supporting the localization-power-boundedness inputs used inside Prop 8.30) and "Cluster E" (Wedhorn 6.18 chain that the project still has stated separately but which is **not** on the clean route per the prior reply).

The project also has separate **Cluster F** (refinement-tree machinery encoding Lemma 8.34 step (ii)–(iv) — Wedhorn's standard-cover existence + a project-specific `RatioLaurentTree`) and **Cluster G/I/H/K** (support infrastructure).

---

## 4. Definitions (project-specific encodings)

The reviewer saw these in the prior brief; recalling briefly:

- **`RationalLocData`** $= (P, T, s)$ with $P$ a pair of definition, $T$ finite, $s \in A$, plus the openness condition that $\{t/s\}$ generates a power-bounded set in $A_s$.
- **`presheafValue D`** $= \widehat{A_s}$ in the canonical $f$-adic topology of Wedhorn §8.1 — the Lean encoding of $A\langle T/s \rangle = \mathcal{O}_X(R(T/s))$.
- **`RationalCovering`** $= (D_{\mathrm{base}}, (D_i)_i)$ with each $D_i$ a rational sub-locale of $D_{\mathrm{base}}$ and the $D_i$ jointly covering $R(T_{\mathrm{base}}/s_{\mathrm{base}})$.
- **`IsSheafy`** (typeclass) — for every rational covering, the product restriction is a topological embedding and compatible families glue.
- **`HasLocLiftPowerBounded`** (typeclass) — packages "$s_V$ image is a unit in $\mathcal{O}_X(U)$" and "$t_V/s_V$ is power-bounded in $\mathcal{O}_X(U)$" for $U \subseteq V$ rational.
- **`IsStronglyNoetherian`** (typeclass) — every Tate algebra over $A$ in finitely many variables is noetherian.
- **`IsTateRing.principalPair`** — non-canonical choice of pair-of-definition + topologically nilpotent unit for a Tate ring.

---

## 5. Established results (sorry-free, for reviewer reference)

- Discrete case of `IsSheafy` (Wedhorn 8.28(c)).
- `productRestriction_faithfullyFlat_abstract` (the Cor 8.32 abstract skeleton: given component flatness + Spec-surjectivity, conclude faithful flatness).
- Stacks 023N descent equalizer decomposed as K.1.a, K.1.b, K.1 (K.1.c is in the catalog as I1).
- Lane-C topological-inducing chain (~20 lemmas, T273–T291 in the project's tickets).
- Wedhorn 8.30 flatness for Laurent-minus restrictions via Wedhorn 8.31(2) + Lemma 2.13 transport (`flat_over_base_tate_laurent`).
- Refinement transfer (`separation_of_finer_rational`, `gluing_of_finer_rational`).
- **Session 19/20 closures**: D3 `mulArchimedean_of_rankOne_valueGroup` (elementary), D4 `mulArchimedean_valueGroup_of_analytic`, D11 `maxIdeal_isClosed_of_complete_huber` (Wedhorn 7.51 part 1), D13 `isUnit_iff_ne_zero_on_spa_of_complete` (Wedhorn 7.52(2)), D15 `units_eq_union_translates_of_oneAdd_topNilp` (after signature fix added `[CompleteSpace A]`), D16 `isOpen_units_of_complete_huber`.

---

## 6. The cluster taxonomy (recap)

Same cluster letters as the prior brief, with current sorry counts after Session 21 deletions:

| Cluster | Description | Sorries | Notes |
|---------|-------------|--------:|-------|
| **A** | Top-level IsSheafy variants | 3 | A1 parametric, A2 hSpa-parametric, A3 Wedhorn-exact (A3 SUSPECT) |
| **B** | Direct dependencies of A | 5 | B2/B3/B4 DELETED; B1, B5, B6, B7, B8 remain (B5 SUSPECT) |
| **C** | Wedhorn-clean wrappers | 5 | C1–C5 |
| **D** | Wedhorn 7.40–7.52 chain | 10 | 6 closed; D1, D2, D5–D10, D12, D14 remain |
| **E** | Wedhorn 6.18 module-uniqueness chain | 4 | E1 false-as-stated; E2 hypothesis-tightened in Stage 1; E3/E4 remain |
| **F** | Refinement-to-standard-cover + Lemma 8.34 tree | 12 | F2/F3 scope-error; F5 SUSPECT; F1, F4, F6–F12 remain |
| **G** | Restriction-map scaffolding | 1 | G3 only (G1/G2 + `restrictionMap_isLocalization` DELETED) |
| **H** | Wedhorn 7.31, 7.32, 7.35 | 4 | H3/H4 out of scope (depend on excluded SpvAI cluster) |
| **I** | Stacks 023N + Wedhorn 8.33 + continuity | 3 | I2 SUSPECT (edge case) |
| **K** | Mis-located scaffolding | 2 | K1, K2 |
| **N** | New honest sorries from Session-21 cascade | 4 | Bodies sorried after consumer of deleted lemmas |

**Total in-scope: ~52 sorries**, of which **4 are flagged SUSPECT by Session 22** (A3, B5, F5, I2) on top of the 6 already flagged as false/scope-error (E1, E2, F2/F3, plus the 4 SUSPECT).

---

## 7. Per-leaf catalog with accuracy + cascade questions

For each leaf the format is:

> **Lname** — *(informal mathematical name)*
>
> **Statement**: mathematical English statement of what the Lean signature claims.
>
> **Cited source**: Wedhorn / Stacks / BGR / project-internal.
>
> **Current discharge route**: how the project intended to discharge this.
>
> **Session-22 accuracy verdict**: ✓ / ⚠ flag.
>
> **Accuracy-Q**: explicit question for the reviewer about the statement.
>
> **Cascade-Q**: explicit question about the discharge route.

For leaves where the answers are obvious (statement clearly accurate, route clearly direct mathlib lemma) the questions are perfunctory. For SUSPECT leaves they are detailed.

### Cluster A — Top-level IsSheafy variants

**A1** — *parametric IsSheafy for strongly noeth Tate with explicit noeth pair*.

- Statement: for $A$ strongly noeth Tate (plus T2, NonarchimedeanRing, IsDomain) and a pair of definition $P$ with $P.A_0$ noetherian, $\mathcal{O}_X$ on $\mathrm{Spa}(A, A^{+})$ is `IsSheafy`.
- Source: Wedhorn 8.28(b) parametric variant.
- Discharge: composition of B6 (topological inducing) and B7+B8 (separation + gluing), using $(P, [\mathrm{IsNoetherianRing}\, P.A_0])$ where needed downstream.
- Verdict: ✓ statement, ⚠ blocked on the chain.
- Accuracy-Q: is the parametric statement correct?
- Cascade-Q: does the proof actually need $[\mathrm{IsDomain}\,A]$? The reviewer flagged G2's $A = k\langle T,U \rangle / (TU)$ counterexample; does that propagate to A1?

**A2** — *hSpa- and topo-inducing-parametric IsSheafy*.

- Statement: same conclusion as A1, but additionally takes the Spa-points witness (primes lift to Spa-points in rational opens) and the topological-inducing witness (for `productRestrictionSub`) as explicit hypotheses.
- Discharge: routine combination of the hypotheses.
- Verdict: ✓.
- Accuracy-Q: this is a clean parametric wrapper; reviewer just confirms.
- Cascade-Q: same IsDomain concern as A1.

**A3** — *Wedhorn-exact IsSheafy for strongly noeth Tate*. **SUSPECT (Session 22)**.

- Statement: for $A$ strongly noeth Tate (T2, NonarchimedeanRing), $\mathcal{O}_X$ is `IsSheafy`. **No $P$ parameter, no IsDomain.** This is the Wedhorn-stated form of Theorem 8.28(b) Case (b).
- Source: Wedhorn 8.28(b) verbatim.
- Discharge: Wedhorn's proof reduces Case (b) to Case (a) (the noetherian-A_0 case) via Wedhorn Remark 6.18 / Definition 6.36 — i.e., the chain we just deleted as B2/B3/B4.
- Verdict: ⚠ statement matches Wedhorn but discharge route is now blocked.
- **Accuracy-Q (A3.acc)**: Is A3's statement actually a theorem of Wedhorn for strongly noeth Tate **without** further hypotheses, or does Wedhorn implicitly assume a noetherian ring of definition exists? In other words: is Wedhorn 8.28(b) for Case (b) actually proved by Wedhorn in full generality, or is the "(b)⇒(a) reduction via 6.18" the only route Wedhorn provides?
- **Cascade-Q (A3.cas)**: If A3 has no alternative route in the strongly-noeth-Tate-only setting (per Q1 of the prior reply), should the project (a) delete A3 entirely keeping only the parametric A1/A2, (b) restate A3 to take an explicit noeth-pair parameter (making it an alias of A1), or (c) keep A3 sorry'd with a permanent open-status documentation? Which is consistent with the policy you laid out (do not keep false scaffolding in the main theorem path)?

### Cluster B — Direct dependencies

**B1** — *`HasLocLiftPowerBounded` instance from strongly noeth Tate*.

- Statement: strongly noeth Tate ⇒ for every rational $U \subseteq V$, the image of $s_V$ in $\mathcal{O}_X(U)$ is a unit, AND $t_V/s_V$ is power-bounded in $\mathcal{O}_X(U)$ for every $t \in T_V$.
- Source: Wedhorn 7.52(2) + 7.41 applied to $\mathcal{O}_X(U)$ (again strongly noeth Tate by Ex 6.38).
- Discharge: via D5 (Wedhorn 7.41) applied at the $\mathcal{O}_X(U)$-level + D13 (already closed).
- Verdict: ⚠P feasible-but-blocked.
- Accuracy-Q: is the statement correct, including the choice of typeclass profile (no `(P)`, no IsDomain)?
- Cascade-Q: B1 depends transitively on the Spa-points machinery B5 (which is itself SUSPECT). Does the 7.52(2) proof at the $\mathcal{O}_X(U)$-level inherit the same noeth-A_0 blocker? If so, B1 is also a SUSPECT, and the entire "Wedhorn-exact no-parameter" architecture collapses.

**B5** — *Spa-points lift above every prime in every rational open*. **SUSPECT (Session 22)**.

- Statement: for $A$ strongly noeth Tate, every finite $T \subseteq A$, every $s \in A$, every prime $\mathfrak{p}$ with $s \notin \mathfrak{p}$, there exists $v \in R(T/s)$ with $\mathfrak{p} \subseteq \mathrm{supp}(v)$.
- Source: Wedhorn Lemma 7.45 chain.
- Discharge: open-prime case via direct construction; non-open-prime case via Wedhorn 7.45 + Chevalley dominating valuation. The Chevalley construction needs a noetherian $A_0$ for the continuity discharge of the lifted valuation.
- Verdict: ⚠ same noeth-A_0 blocker as A3.
- **Accuracy-Q (B5.acc)**: is Wedhorn 7.45 actually proved without a noetherian ring of definition? Or does Wedhorn's proof implicitly use it (and the strongly-noeth-Tate-only statement is open in the literature)?
- **Cascade-Q (B5.cas)**: same options as A3 — delete, restate parametrically, or keep sorry'd with documentation? B5 is consumed by B1 (HasLocLiftPowerBounded) and indirectly by C2 (cor_8_32_clean via Spa-point cover surjectivity); the cascade from B5 is broader than A3's.

**B6** — *Topological inducing of `productRestrictionSub`*.

- Statement: for every rational covering $C$, the product restriction $\mathcal{O}_X(C_{\mathrm{base}}) \to \prod_i \mathcal{O}_X(C_i)$ is a topological inducing map (gives subspace topology).
- Source: project's Gap B (no direct Wedhorn citation; equivalent to the Lane-C single-step closer + the Wedhorn 8.34 refinement-tree assembly F4).
- Discharge: Lane C done (T273–T291); needs F4 (refinement-tree existence) to assemble.
- Verdict: ✓ statement, ⚠P feasible.
- Accuracy-Q: confirm that topological inducing is the right strength (not just continuity), given downstream use in `IsSheafy.embedding`.
- Cascade-Q: any concern that B6 is similarly load-bearing on something post-deletion?

**B7** — *Tate acyclicity Part 1 (separation) via Cor 8.32*.

- Statement: for $A$ strongly noeth Tate, $x \in \mathcal{O}_X(C_{\mathrm{base}})$ vanishing on every $\mathcal{O}_X(C_i)$ implies $x = 0$.
- Source: Wedhorn Cor 8.32 "in particular, injective" consequence.
- Discharge: directly from C2 (`cor_8_32_clean`).
- Verdict: ✓ statement, ⚠P blocked on C2.
- Accuracy-Q: confirm.
- Cascade-Q: confirm C2-route is the correct unblocker.

**B8** — *Tate acyclicity Part 2 (gluing) via faithfully flat descent*.

- Statement: compatible families on a rational cover glue to a global section.
- Source: Wedhorn Lemma 8.34 $H^0$ content + faithfully flat descent equaliser (Stacks 023N).
- Discharge: I1 (Stacks 023N K.1.c) + C2 (Cor 8.32) + F12 (descent through refinement).
- Verdict: ✓ statement, ⚠P blocked on I1 + F12.
- Accuracy-Q: confirm.
- Cascade-Q: confirm.

### Cluster C — Wedhorn-clean wrappers

**C1** — *Prop 8.30 flat restriction (Wedhorn-clean form)*.

- Statement: for $A$ strongly noeth Tate, $U \subseteq V$ rational, $\mathcal{O}_X(V) \to \mathcal{O}_X(U)$ is flat.
- Source: Wedhorn Prop 8.30.
- Discharge: Wedhorn's proof: by Ex 6.38 reduce to $V = X$, then Lemma 8.31 gives flatness for Laurent shapes, then arbitrary rational $U$ via Laurent decomposition (project has the chain `T-RATIONAL-FLAT-GENERAL`).
- Verdict: ✓ statement, ⚠P blocked on the Lemma 8.31 wrappers and B-level canonical-form assembly.
- Accuracy-Q: the project's discharge needs project-internal "B-level canonical-form hypotheses" (`hb`, `hT_pb`, `hcont_eval` for the relative datum) — are these actually canonical, or are they hiding additional content?
- Cascade-Q: with L1/L2/L3 (the AuditPass1 Wedhorn 8.31 wrappers) deleted, what's the cleanest route to discharge C1 — restate L1/L2/L3 parametrically, or invoke Wedhorn 8.31 inside the project's existing `flat_over_base_tate_laurent` chain?

**C2** — *Cor 8.32 product faithfully flat (Wedhorn-clean form)*.

- Statement: for $A$ strongly noeth Tate, $C$ a finite rational covering, the product restriction $\mathcal{O}_X(C_{\mathrm{base}}) \to \prod_i \mathcal{O}_X(C_i)$ is faithfully flat.
- Source: Wedhorn Cor 8.32.
- Discharge: C1 component flatness + B5-style Spa-point surjectivity (giving Spec-surjectivity by faithful-flatness criterion).
- Verdict: ✓ statement, ⚠P blocked on C1 + (something B5-equivalent).
- Accuracy-Q: the Spa-point-to-Spec-prime translation requires the B5 chain. If B5 is unprovable in the no-pair-of-definition setting, can C2 still be discharged via a different Spec-surjectivity argument?
- Cascade-Q: with B5 SUSPECT, is C2 also SUSPECT by the same chain?

**C3** — *Spa-presheafValue homeomorphism (Wedhorn 8.2)*.

- Statement: $\mathrm{Spa}(\mathcal{O}_X(D), \cdot)$ is homeomorphic to the rational subset $R(D.T / D.s) \cap \mathrm{Spa}\,A$.
- Source: Wedhorn Prop 8.2.
- Discharge: needs project-internal Spa.comap framework (Wedhorn 8.7). API gap.
- Verdict: ✓ statement, ⚠H blocked on API gap.
- Accuracy-Q: confirm Wedhorn 8.2 statement.
- Cascade-Q: any concern with the Spa.comap framework Lemma 8.7 itself?

**C4** — *`presheafValue D` is a Tate ring (Wedhorn-clean)*.

- Statement: for $A$ strongly noeth Tate and $D$ rational, $\mathcal{O}_X(D)$ is Tate.
- Source: Wedhorn Example 6.38.
- Discharge: project's Example638.lean (sorry-free).
- Verdict: ✓ statement, ○ readily feasible (project discharges).
- Accuracy-Q: confirm.
- Cascade-Q: none expected.

**C5** — *`presheafValue D` is noetherian (Wedhorn-clean)*.

- Statement: for $A$ strongly noeth Tate and $D$ rational, $\mathcal{O}_X(D)$ is noetherian.
- Source: Wedhorn Example 6.38.
- Discharge: project's Example638.lean.
- Verdict: ✓ statement, ○ feasible.
- Accuracy-Q: confirm.
- Cascade-Q: confirm Ex 6.38 is correctly stated (no implicit noeth-A_0 hypothesis hiding in the project's encoding).

### Cluster D — Wedhorn 7.40–7.52

**D1** — *Analytic continuous valuations have non-vanishing topologically nilpotent witnesses*.

- Statement: $A$ Huber; $x \in \mathrm{Cont}(A)$ with non-open support ⇒ ∃ $a \in A^{\circ\circ}$ with $x(a) \ne 0$.
- Source: Wedhorn 7.40(1).
- Discharge: direct valuation argument.
- Verdict: ✓.
- Accuracy-Q: confirm Wedhorn 7.40(1) verbatim.
- Cascade-Q: none expected.

**D2** — *Analytic ⇒ rank-1 value group*.

- Statement: $A$ Huber; $x$ analytic ⇒ value group of $x$ admits an order-monomorphism into $(\mathbb{R}_{>0}, \cdot)$.
- Source: Wedhorn 7.40(5).
- Discharge: Hahn embedding for ordered groups + 7.40(5) microbiality.
- Verdict: ✓.
- Accuracy-Q: confirm.
- Cascade-Q: none expected; statement matches Wedhorn 7.40(5).

**D5** — *Analytic + height-1 + power-bounded ⇒ $v(a) \le 1$ (Wedhorn 7.41)*.

- Statement: $A$ Huber; $x \in \mathrm{Cont}(A)$ analytic; $a \in A^{\circ}$ ⇒ $x(a) \le 1$.
- Source: Wedhorn Prop 7.41.
- Discharge: contradiction via D4 + 7.40(1).
- Verdict: ✓.
- Accuracy-Q: the Lean signature drops the explicit "height 1" hypothesis (since analyticity implies it via D2). Is this transcription correct?
- Cascade-Q: none expected.

**D6** — *Algebraic-side power-boundedness of $t_V/s_V$ lift in `Localization.Away`*.

- Statement: project-side intermediate: $\mathrm{IsLocalization.Away.lift}\, D.s \,h \,(t/s)$ is power-bounded in $\mathrm{Localization.Away}\,D'.s$ with the localization topology.
- Source: assembled (not direct Wedhorn).
- Discharge: T-H.2.b decomposition.
- Verdict: ✓ (intermediate algebraic step).
- Accuracy-Q: confirm.
- Cascade-Q: any hidden noeth-A_0 dependence?

**D7** — *Completion-side power-boundedness in `presheafValue`*.

- Statement: same as D6 but in $\mathcal{O}_X(U) = \mathrm{presheafValue}\,U$.
- Source: D5 applied to $\mathcal{O}_X(U)$ (strongly noeth Tate again by Ex 6.38).
- Discharge: D5 + Ex 6.38.
- Verdict: ✓.
- Accuracy-Q: confirm.
- Cascade-Q: D5 at the $\mathcal{O}_X(U)$-level requires strongly-noeth-Tate at $\mathcal{O}_X(U)$. With Ex 6.38 in hand, this is fine. Confirm no other hidden dependency.

**D8** — *Power-bounded $\iff$ $v(a) \le 1$ for all continuous $v$ (assembled, mis-cited as "Wedhorn 7.42")*.

- Statement: $A$ complete Huber; $a \in A$ is power-bounded ⇔ $v(a) \le 1$ for every $v \in \mathrm{Cont}(A)$.
- Source: assembled from Wedhorn 7.41 (analytic case) + non-analytic argument via 7.40(5) generizations. **NOT** Wedhorn Remark 7.42 (which is about vertical generizations of $\Gamma_x$). Lemma name retained for legacy.
- Discharge: D5 + non-analytic argument.
- Verdict: ⚠S citation imprecise; content correct.
- Accuracy-Q: confirm the assembled statement is correct, and confirm Wedhorn 7.42 is the wrong citation (we have a Stage-1 docstring fix in place).
- Cascade-Q: rename — what's the correct citation? "Huber/Wedhorn power-bounded valuation criterion" is the current placeholder.

**D9** — *Dominating valuation subring construction (Wedhorn 7.45 intermediate)*.

- Statement: $A$ Huber, $\mathfrak{p}$ prime, $s \notin \mathfrak{p}$, $T$ finite ⇒ ∃ valuation subring $B \subseteq \mathrm{Frac}(A/\mathfrak{p})$ that dominates the image of $A_0$ in $\mathrm{Frac}(A/\mathfrak{p})$, contains the image of $\{t/s\}_{t \in T}$, and contains the image of $I \cdot A_0$ in its non-units.
- Source: standard Chevalley dominating-valuation extension, backing Wedhorn 7.45.
- Discharge: Chevalley construction + bookkeeping. **API gap** — significant.
- Verdict: ✓ statement, ⚠H API gap.
- Accuracy-Q: confirm the formulation matches Wedhorn 7.45's needs.
- Cascade-Q: does the Chevalley extension require any extra hypothesis on $A_0$ (e.g. noetherian)? If yes, this inherits the A3/B5 SUSPECT status.

**D10** — *`exists_mem_rationalOpen_supp_ge_of_prime_noHArch` (Wedhorn 7.45)*.

- Statement: $A$ complete Huber Tate with $[\mathrm{IsAdicComplete}\,P.I\,P.A_0]$; prime $\mathfrak{p}$, $s \notin \mathfrak{p}$, $T$ finite ⇒ ∃ $v \in R(T/s)$ with $\mathfrak{p} \subseteq \mathrm{supp}(v)$.
- Source: Wedhorn Lemma 7.45 (non-open prime case).
- Discharge: D9 + completion-lift.
- Verdict: ✓.
- Accuracy-Q: this version DOES take $P$ + `[IsAdicComplete P.I P.A_0]` as a parameter — does it take enough? Specifically, does `[IsAdicComplete P.I P.A_0]` suffice, or do we additionally need `[IsNoetherianRing P.A_0]`?
- Cascade-Q: confirm D10 is the right parametric form of B5.

**D12** — *Trivial-valuation Spa-point above a maximal ideal (Wedhorn 7.51 part 2)*.

- Statement: $A$ complete affinoid, $\mathfrak{m}$ maximal ⇒ ∃ $v \in \mathrm{Spa}(A, A^{+})$ with $\mathrm{supp}(v) = \mathfrak{m}$.
- Source: Wedhorn Prop 7.51 part 2.
- Discharge: residue field $A/\mathfrak{m}$ is a complete non-arch field (using D11 + completeness inheritance); trivial valuation lifts to Spa. **API gap** — non-discrete trivial-valuation construction is substantial.
- Verdict: ✓ statement, ⚠H API gap.
- Accuracy-Q: confirm. Note that Wedhorn's proof goes through a non-trivial use of completeness of the residue field; what's the minimal "complete non-arch field" infrastructure needed?
- Cascade-Q: any hidden noeth-A_0 dependence in Wedhorn 7.51 part 2's proof?

**D14** — *Topologically nilpotent elements = union of definition ideals*.

- Statement: $A$ Huber: $A^{\circ\circ} = \bigcup_P P.I$ over pairs of definition (image in $A$).
- Source: used inside Wedhorn 7.51 proof, p.69.
- Discharge: easy direction direct; hard direction needs **enlargement-of-definition-rings** (project's `AdjoinFinset` machinery). API gap.
- Verdict: ✓ statement, ⚠H API gap.
- Accuracy-Q: confirm.
- Cascade-Q: the enlargement-of-definition-rings argument is a project-internal "factor through a larger noeth A_0" — does this require any extra hypothesis we don't have?

### Cluster E — Wedhorn 6.18 chain

(Cluster E is the chain that the prior reviewer told us **not** to use in the main path. We keep them stated but the dependency arrow from IsSheafy to Cluster E is broken — Cluster E is now orphaned support infrastructure. The questions below are about whether they're worth keeping at all.)

**E1** — *`_sub_lemma_L3_1a_completion_fg_complete` (BGR §3.7.2/1 with wrong hypothesis bundle)*.

- Statement: $A$ complete + cg-uniformity; $M$ fg Hausdorff $A$-module ⇒ $M$ complete.
- Source: claim "BGR §3.7.2/1".
- Verdict: ⚠F FALSE-AS-STATED (b2_log entry #1). Counterexample: $A = \mathbb{Z}$ discrete, $M = \mathbb{Z}$ $p$-adic; $M$ fg over $A$ but $\hat{M} = \mathbb{Z}_p \ne M$.
- Accuracy-Q: confirm the BGR §3.7.2/1 statement actually requires "completion is fg", not "module is fg"?
- Cascade-Q: if E1 is restated correctly (with the $\hat{M}$-fg hypothesis), what downstream consumers in Cluster E need to be rewired? Is the whole Cluster E chain still useful for anything in the IsSheafy path, or should we delete it entirely as orphaned infrastructure?

**E2** — *`wedhorn_6_18_unique` (uniqueness of fg-module topology, hypothesis-tightened in Stage 1)*.

- Statement: $A$ complete noeth Tate; $M$ fg ⇒ ∃! uniform structure $\tau$ on $M$ with: UAG + complete + cg + T2 + ContinuousSMul; and any other $\tau'$ satisfying the same constraints has $\tau.\mathrm{topology} = \tau'.\mathrm{topology}$.
- Source: Wedhorn Prop 6.18(1) uniqueness.
- Verdict: ⚠ Stage-1 signature tightening added `[ContSMul τ']` (b2_log entry #2 fix); body still sorried.
- Accuracy-Q: with the Stage-1 added typeclasses, is the statement now correct?
- Cascade-Q: is E2 used anywhere in the IsSheafy path post-deletion? If not, delete?

**E3** — *Stacks 0316: I-adic completion of noeth ring is noeth*.

- Statement: $R$ noetherian commutative, $I$ ideal ⇒ $\widehat{R}$ ($I$-adic completion) is noetherian.
- Source: Stacks tag `0316` = Lemma 10.97.6.
- Discharge: **mathlib gap** — ~150 LOC.
- Verdict: ✓ statement, ⚠H mathlib gap. Citation corrected Stage 1 (was wrongly `00MA`).
- Accuracy-Q: confirm the corrected citation.
- Cascade-Q: is E3 used in the IsSheafy path post-deletion? If only in Cluster E (which is now orphaned), delete?

**E4** — *Inductive step: $A\langle X_1,\ldots,X_k \rangle$ noeth ⇒ $A\langle X_1,\ldots,X_{k+1} \rangle$ noeth*.

- Statement: as above.
- Source: E3 + Hilbert basis theorem.
- Verdict: ✓.
- Cascade-Q: same as E3 — used post-deletion?

### Cluster F — Refinement-to-standard-cover + Lemma 8.34 tree

**F1** — *`exists_standard_cover_refining` (project encoding of W1)*.

- Statement: $A$ strongly noeth Tate; $C$ rational covering ⇒ ∃ $S \subseteq A$ with the project's `refines_cover`/`refines_contain`/`refines_span_top` triple.
- Source: project encoding intended to wrap Wedhorn 7.54.
- Verdict: ⚠ inherits F2/F3 scope error.
- Accuracy-Q: with the relativisation-over-O(C.base) fix the reviewer recommended, what's F1's correct restated form?
- Cascade-Q: how does the F1 restatement interact with the downstream P3–P8 chain (F4 etc.)?

**F2** — *`exists_ideal_generators_refining_cover` (Wedhorn 7.54 directly, mis-scoped)*.

- Statement: $A$ strongly noeth Tate; $C$ rational covering ⇒ ∃ $S \subseteq A$, $\mathrm{Ideal.span}\,S = \top$, each $R(S/f) \subseteq$ some cover piece.
- Source: claim "Wedhorn Lemma 7.54".
- Verdict: ⚠F SCOPE-ERROR (prior reviewer Q3 confirmation).
- Accuracy-Q: confirm the fix per prior reply (relativise over $\mathcal{O}_X(C_{\mathrm{base}})$ — make $S$ live in $\mathcal{O}_X(C_{\mathrm{base}})$, not $A$).
- Cascade-Q: which downstream leaves (F1, F3, F4, ...) inherit this scope error and need restatement?

**F3** — *Packaging of F2*.

- Same as F2; inherits scope error.

**F4** — *Existence of the ratio-Laurent-refinement tree*.

- Statement: $A$ strongly noeth Tate (+ IsDomain, DecidableEq, parametric noeth-pair); $C$ rational covering ⇒ ∃ `RatioLaurentTree` $t$ and realisation $\rho$ such that $\rho$ refines $C$ and every split of $t$ is topologically inducing.
- Source: project encoding of Wedhorn Lemma 8.34's steps (ii)–(iv).
- Discharge: composition of F7+F8+F9+F10.
- Verdict: ✓ statement (project encoding), ⚠P feasible.
- Accuracy-Q: per the prior reviewer Q10, the relative-over-base structure is correct in principle. Is F4 stated correctly relatively? (The IsDomain hypothesis is questionable per F5 below.)
- Cascade-Q: with F2/F3 needing restatement, does F4 need a relativisation matching the F1-restated form?

**F5** — *Wedhorn-exact form of F4 dropping `[IsDomain A]`*. **SUSPECT (Session 22)**.

- Statement: same as F4 but without `[IsDomain A]`.
- Source: aspirational "drop IsDomain to match Wedhorn-stated profile".
- Discharge: would-be direct from F4 if IsDomain weren't needed.
- Verdict: ⚠S the project's `RatioLaurentTree` construction uses non-zero-divisor data (similar to the G2 counterexample). Possibly FALSE without IsDomain.
- **Accuracy-Q (F5.acc)**: does Wedhorn's Lemma 8.34 require an integral-domain hypothesis on $A$, or is it stated for arbitrary strongly noeth Tate $A$ (including potentially non-domain examples like $k\langle T,U \rangle / (TU)$)? If Wedhorn does NOT require IsDomain, can his proof actually go through in non-domain cases — or is there an implicit assumption?
- **Cascade-Q (F5.cas)**: is F5's signature without IsDomain provably false (per the G2 counterexample), and should F5 be deleted in favour of F4? Or is there a relativised reformulation that's true in non-domain cases?

**F6** — *Legacy I.1 wrapper of F4* (similar status).

**F7** — *Step (ii) of Wedhorn 8.34 (first-stage unit-generated Laurent tree)*.

- Statement: project-internal step (ii) packaging.
- Source: Wedhorn 8.34(ii) — uses Cor 7.32 to produce topologically nilpotent unit $s$ with $\{s^{-1} f_i\}$ generating a unit-generated cover.
- Verdict: ✓ statement, ⚠P feasible via H2.
- Accuracy-Q: confirm the project's step (ii) encoding matches Wedhorn.
- Cascade-Q: depends on H2 (finset Cor 7.32). Any concern there?

**F8** — *Step (iii) of Wedhorn 8.34 (unit-generated cover → ratio Laurent refinement)*.

- Statement: project step (iii).
- Verdict: ✓, ⚠P feasible.

**F9, F10** — *Steps (iv) and per-node transport from the relative encoding back to absolute `RationalLocData`*.

- Statement: project-internal transport machinery.
- Verdict: ✓ statement (project encoding), ⚠P feasible.

**F11** — *Consumer of F4 producing topological inducing*.

- Statement: given a refinement tree realisation $\rho$ with all-splits-inducing, `productRestrictionSub C` is topologically inducing.
- Verdict: ✓.

**F12** — *`tateAcyclicity` Part 2 in LaurentRefinement (import-cycle scaffold)*.

- Statement: same as B8 conclusion but stated in LaurentRefinement.lean (preceding Cor832.lean in import order).
- Verdict: ✓ statement, ⚠P blocked by import cycle — needs downstream wiring through `TateAcyclicityFinalAssembly.lean`.

### Cluster G — Restriction-map scaffolding (post-deletion)

**G3** — *Closedness of $\{(x,y) : xy = 0\}$ in $R \times R$ for Hausdorff topological commutative ring $R$*.

- Statement: above.
- Source: general topology.
- Discharge: mathlib `IsClosed.preimage` + diagonal.
- Verdict: ✓, ⚠P feasible (~5 LOC).

### Cluster H — Wedhorn 7.31, 7.32 supporting (in scope)

**H1** — *Wedhorn Lemma 7.31*.

- Statement: $A$ affinoid, $X \subseteq \mathrm{Spa}\,A$ quasi-compact, $f \in A$ with $|f(x)| \ne 0$ on $X$ ⇒ ∃ open nbhd $I$ of $0 \in A$ with $|a(x)| < |f(x)|$ for all $a \in I$, $x \in X$.
- Source: Wedhorn 7.31.
- Verdict: ✓, ⚠H standard but ~120 LOC.
- Accuracy-Q: confirm.
- Cascade-Q: depends on Spa quasi-compactness (which is established sorry-free for Tate case in the project).

**H2** — *Finset form of Wedhorn Cor 7.32*.

- Statement: $A$ Tate affinoid; $T$ finite with $\forall v \exists t \in T, v(t) \ne 0$ ⇒ ∃ unit $s \in A^{\times}$ with $\forall v, \exists t \in T, v(s) < v(t)$.
- Source: Wedhorn Cor 7.32 finset form.
- Discharge: singleton version proved; need product trick over finsets.
- Verdict: ✓, ⚠P feasible.
- Accuracy-Q: confirm.
- Cascade-Q: the product-trick assembly — any concern with the natural per-$t$ dominating units multiplying correctly?

### Cluster I — Stacks 023N + Wedhorn 8.33 + continuity scaffolding

**I1** — *Stacks 023N K.1.c (descent equaliser surjectivity from faithful flatness)*.

- Statement: $R \to S$ faithfully flat; $s \in S$ with $1 \otimes s = s \otimes 1$ in $S \otimes_R S$ ⇒ ∃ $r \in R$ with $r \cdot 1_S = s$.
- Source: Stacks 023N.
- Discharge: mathlib `Module.Flat.tensorEqLocusEquiv` + `ker_lTensor_eq` + standard chase.
- Verdict: ✓, ⚠H feasible (~80 LOC).
- Accuracy-Q: confirm.
- Cascade-Q: confirm the mathlib Flat.Equalizer machinery is sufficient (not requiring further mathlib additions).

**I2** — *Wedhorn Lemma 8.33 generalised (2-element Laurent cover exact for noeth complete Tate $A$ and arbitrary $f \in A$)*. **SUSPECT (Session 22)**.

- Statement: $A$ Huber/Tate/noetherian/complete/T2/NonarchimedeanRing; $f \in A$; then the 4-tuple $(\varepsilon\text{-gen}\,f, \delta\text{-gen}\,f)$ for the 2-element Laurent cover is exact.
- Source: Wedhorn Lemma 8.33, generalised away from `[IsDomain A]` via Krull intersection.
- Discharge: project's `epsilonHom_gen_injective_of_iInf_pow_eq_bot` uses $\bigcap_n (f)^n = (0)$ which is Krull intersection. Krull intersection requires either noeth + domain (then automatic), or $I$ in Jacobson radical, etc.
- Verdict: ⚠S EDGE CASE: for $f$ a unit, $\bigcap_n (\top)^n = \top \ne (0)$, so the Krull-intersection route degenerates.
- **Accuracy-Q (I2.acc)**: does Wedhorn 8.33 implicitly assume $f$ is a non-unit (since the 2-element Laurent cover is degenerate when $f$ is a unit anyway)? Or is the exactness vacuously true for $f$ unit (because the cover trivialises)?
- **Cascade-Q (I2.cas)**: should I2's statement case-split on $f$ a unit vs not, or should the hypothesis be strengthened to exclude units (since the cover is degenerate in that case)?

**I3** — *Iterated plus/minus forward-to-completion continuity (project scaffolding)*.

- Statement: continuity of the iterated forward maps in the Laurent decomposition chain.
- Source: project-internal.
- Verdict: ✓, ⚠P routine.

### Cluster K — Mis-located scaffolding

**K1** — *Spa-point construction for non-open prime in rational subset (Wedhorn 7.45 corollary)*.

- Statement: $A$ Huber; $D \subseteq D_0$ rational; prime $\mathfrak{p}$ with $s_{D_0} \in \mathfrak{p}$, $s_{D'} \notin \mathfrak{p}$, $\mathfrak{p}$ not open ⇒ ∃ $v \in R(D'.T/D'.s)$ with $\mathfrak{p} \subseteq \mathrm{supp}\,v$.
- Source: project corollary of Wedhorn 7.45.
- Verdict: ✓, ⚠P depends on D10.

**K2** — *`restrictionMapAlg_continuous_of_huber_completion` (transport continuity scaffolding)*.

- Statement: continuity of algebraic-to-completion restriction lift under power-boundedness on lifted generators.
- Source: project continuity scaffolding.
- Verdict: ✓, ⚠P depends on D7.

### Cluster N — New honest sorries from Session-21 deletion cascade

**N1** — *`flat_over_base_tate` body (Cor832.lean) sorried after deletion of `restrictionMap_isLocalization`*.

- Statement: for $A$ strongly noeth Tate with $(P, [\mathrm{IsNoetherianRing}\,P.A_0])$, each restriction in cover is flat.
- Source: Wedhorn Prop 8.30 specialised.
- Verdict: ✓ statement; ⚠P blocked.
- Accuracy-Q: confirm.
- Cascade-Q: should N1 route through C1 (`prop_8_30_flat_clean`), or directly through `flat_over_base_tate_laurent_combined`? The latter requires the cover to be Laurent-shape; the former is full generality.

**N2** — *`hSpa_surj_from_spanTop` body sorried after deletion of `restrictionMap_isLocalization`*.

- Statement: given span-top hypothesis on the canonical-map images, every prime of base lifts to a prime of some cover piece.
- Source: prime-extension via Cor 8.32.
- Verdict: ✓ statement; ⚠P blocked.
- Accuracy-Q: confirm.
- Cascade-Q: this needs either C2 (circular with B7) or a direct Spa-point construction at the cover-piece level. Which is the cleaner unblocker?

**N3** — *`tateAcyclicity` Part 1 separation body (LaurentRefinement.lean) sorried*.

- Same as B7.

**N4** — *`tateAcyclicity_gluing_via_refinement` per-E separation body (LaurentRefinement.lean) sorried*.

- Statement: per-$E$ separation lemma used inside the refinement-transfer of gluing.
- Source: per-$E$ Cor 8.32 product injectivity.
- Verdict: ✓ statement; ⚠P blocked by import cycle.

---

## 8. Where we're stuck (meta-level)

The leaf-by-leaf catalog above gives the per-leaf picture. At the meta level, three structural issues:

**S1 — The Wedhorn-exact no-parameter route may not exist.** A3 + B5 + (B1, C2 inheriting) together encode "from `[IsStronglyNoetherian A]` alone, derive the same content the deleted B2/B3/B4 chain claimed". The prior reviewer told us deleting B2/B3/B4 was correct. But the downstream wrappers A3/B5 are now in the same position: they have no proof route in the project's setting unless the existence of a noetherian ring of definition is supplied externally (which it cannot be for $\mathbb{C}_p$). Either (a) the Wedhorn-exact no-parameter route is genuinely possible via a different proof than Wedhorn's stated 6.18 chain, (b) the project should adopt the parametric form everywhere, or (c) some leaves should be deleted as having no salvageable proof route in scope.

**S2 — The IsDomain hypothesis is doing work somewhere.** A1/A2 require `[IsDomain A]`; the prior reviewer noted G2 counterexample $A = k\langle T,U \rangle / (TU)$. Does the IsDomain assumption propagate through every part of the chain (Wedhorn 8.30, 8.32, 8.34) or only through specific steps (Laurent split, refinement-tree construction)? F4 needs IsDomain; F5 drops it and is now SUSPECT. If we keep IsDomain at the top level (A1/A2), we should know exactly which sub-lemmas inherit it; if we want to remove it, we need to know which sub-lemmas need restatement.

**S3 — The Cluster E orphan.** Cluster E (Wedhorn 6.18 module-uniqueness chain) is no longer on any path to IsSheafy after the prior reviewer told us not to route through it. The four leaves E1, E2, E3, E4 currently sit as orphaned sorries. Should they be deleted entirely, or are they salvageable for some independent purpose?

---

## 9. Open mathematical questions for the reviewer

The per-leaf accuracy + cascade questions are in §7. The catalog has ~52 leaves with ~100 individual questions. We do **not** expect a per-leaf paragraph back — we expect:

- A pass-through of §7 noting where you agree with our verdicts ("the ✓ leaves all look fine") and where you have concerns ("D9 needs noeth A_0 too").
- Detailed responses to the SUSPECT leaves A3, B5, F5, I2 (these are the ones we most need a verdict on).
- The meta-questions below.

### Q-META.1 — Wedhorn 8.28(b) Case (b) without noeth-A_0

> Does Wedhorn 8.28(b) Case (b) — strongly noetherian Tate $A$ (with no further noetherian-ring-of-definition hypothesis) ⇒ $\mathcal{O}_X$ is a sheaf — actually have a proof in the literature that does NOT route through Wedhorn 6.18 forward / Wedhorn 8.28(a) reduction? If yes, what's the citation? If no, should the Lean project (i) accept that A3 is unprovable as stated and delete it, (ii) restate A3 with an explicit noetherian-ring-of-definition parameter, or (iii) restrict the entire project to the BGR 5.2.6 height-1 setting where the noetherian ring of definition is automatic?

### Q-META.2 — The cascade audit policy

> The previous brief asked you about a few directly-suspect leaves (B2/B3/B4, F2/F3). You confirmed those as false. We deleted them. We then discovered (Session 22) that several remaining leaves — including A3/B5/B1/C2 — are load-bearing on the same Wedhorn 6.18 chain in their proof routes, not just in their (deleted) explicit dependencies. The prior brief did not surface those because we only asked about the directly-suspect leaves, not their cascade. Going forward, what's the right policy for surfacing cascade dependencies before sending a brief? Should every brief have a "for each false leaf X, list downstream consumers Y that route through X in their proof, and ask whether Y survives" pre-flight? Or is there a sharper diagnostic you'd recommend?

### Q-META.3 — IsDomain hypothesis

> The G2 counterexample ($A = k\langle T,U \rangle / (TU)$) is a strongly noetherian Tate ring that's not a domain. Wedhorn states 8.28(b) for strongly noetherian Tate, without IsDomain. Yet the project's IsSheafy chain currently has `[IsDomain A]` in A1/A2 and uses it in the Laurent-split machinery (F4 etc.). Is Wedhorn 8.28(b) genuinely a theorem for non-domain strongly noetherian Tate rings? If so, what's the standard route — does Wedhorn handle non-domain cases via a different argument, or is the project's reliance on Laurent splits forcing the IsDomain hypothesis?

### Q-META.4 — Cluster E disposition

> Cluster E (Wedhorn 6.18 module-uniqueness chain — E1, E2, E3, E4) is no longer used in any path to IsSheafy after we adopted your recommendation to keep `[IsStronglyNoetherian A]` explicit. Should we delete the entire Cluster E? Or are E1 (BGR §3.7.2/1 completion), E2 (uniqueness), E3 (Stacks 0316), E4 (Hilbert-basis inductive step) useful for some downstream use we're missing?

### Q-META.5 — High-leverage targets

> Among the remaining ~30 ⚠P leaves (accurate-but-blocked-on-project-assembly), which would you prioritise as the most leveraged for unblocking the chain? Our Session-22 guess was: C1 (Prop 8.30 clean), F4 (refinement tree), I1 (Stacks 023N K.1.c). Do you agree, or would you sequence differently?

### Q-META.6 — The four explicit SUSPECT leaves

> Concrete decisions wanted on each:
>
> 1. **A3** `isSheafy_ofStronglyNoetherianTate` (no $P$): delete / restate parametric / keep sorry'd?
> 2. **B5** `exists_hSpa_points_global_*` (no $P$): same options.
> 3. **F5** `*_clean` form of F4 dropping `[IsDomain A]`: delete / keep IsDomain / find non-domain restatement?
> 4. **I2** `laurentCover_exact_general`: case-split on $\mathrm{IsUnit}\,f$ / restrict statement / leave with documented gap?

### Q-META.7 — Any other leaves we should be SUSPECT of?

> The Session-22 audit found four SUSPECT leaves (A3, B5, F5, I2). Looking at the ~30 remaining ⚠P leaves in §7, do you see any others that strike you as plausibly load-bearing on something deleted or on an unproved cascade — i.e., the same "✓ on paper but actually load-bearing" pattern as A3?

---

## 10. Document metadata

- Project name: Adic Spaces (Lean formalisation of Wedhorn's textbook)
- Brief generated: 2026-05-18 (Session 22)
- Length: ~13 pages of mathematical English + ~52-leaf catalog
- Build status: clean; ~120 total sorries (~52 in IsSheafy chain); no errors
- Recent commit context: Session 21 deletions (9 false-as-stated declarations); Session 22 audit (4 additional SUSPECT leaves flagged)
- Prior brief: `expert-review/2026-05-18/brief.md` (and its reply, which guided the Session 21 deletions)
- Reference list above includes all sources cited in the per-leaf catalog
