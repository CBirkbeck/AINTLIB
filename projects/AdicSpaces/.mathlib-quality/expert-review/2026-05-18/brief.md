# Review brief — Lean 4 formalisation of Tate acyclicity (Wedhorn Theorem 8.28(b))

*Prepared 2026-05-18 for a mathematical-model reviewer (ChatGPT / Claude class).
Self-contained: no repository access required.
Combined goal: (1) soundness check on four flagged statements; (2) strategic guidance on the project as a whole.*

---

## 1. Goal

We are formalising **Wedhorn Theorem 8.28(b)** in Lean 4 on top of Mathlib: for an affinoid ring $(A, A^{+})$ with $A$ a strongly noetherian Tate ring, the presheaf $\mathcal{O}_X$ on the adic spectrum $X := \mathrm{Spa}(A, A^{+})$ is a sheaf of complete topological rings, and $H^q(U, \mathcal{O}_X) = 0$ for all $q \ge 1$ and all rational subsets $U \subseteq X$.

The current Lean target encapsulates the **sheaf-of-sets** half (existence + uniqueness of glueings + topological-embedding control), packaged in a typeclass `IsSheafy`. The higher cohomology vanishing $q \ge 1$ is scoped out of the current target.

Approximately **55 `sorry`-bodied lemmas across 11 files** sit in the transitive dependency closure of this target. This brief enumerates all of them, identifies five whose stated form appears mathematically false / open / mis-cited, and asks for strategic guidance.

---

## 2. Background and references

### 2.1. Setting

All rings are commutative with $1$. "Topological ring" means a ring with a ring topology; "complete" means complete as a uniform space.

- An **$f$-adic ring** $A$ has an open subring of definition $A_0 \subseteq A$ which is $I$-adic for a finitely generated ideal $I \subseteq A_0$ (the **ideal of definition**); the pair $(A_0, I)$ is a **pair of definition**.
- A **Tate ring** is an $f$-adic ring with a topologically nilpotent unit $\pi$.
- $A^{\circ} \subseteq A$ denotes the subring of power-bounded elements; $A^{\circ\circ}$ the ideal of topologically nilpotent elements.
- A **ring of integral elements** $A^{+} \subseteq A^{\circ}$ is an integrally-closed open subring containing $A^{\circ\circ}$; the pair $(A, A^{+})$ is an **affinoid ring**.
- $\mathrm{Spv}(A)$ = equivalence classes of valuations $v: A \to \Gamma \cup \{0\}$ for $\Gamma$ totally ordered abelian.
- $\mathrm{Cont}(A) \subseteq \mathrm{Spv}(A)$ = continuous valuations.
- $\mathrm{Spa}(A, A^{+}) := \{v \in \mathrm{Cont}(A) : v(f) \le 1 \text{ for all } f \in A^{+}\}$.
- For $T \subseteq A$ finite with $T \cdot A$ open, and $s \in A$, the **rational subset** is
$$
R(T/s) := \{v \in \mathrm{Spa}(A, A^{+}) : v(t) \le v(s) \ne 0 \text{ for all } t \in T\}.
$$
- $\mathcal{O}_X(R(T/s)) := A\langle T/s \rangle$, the completion of the topological localisation $A_s$ with the unique non-archimedean topology making $\{t/s : t \in T\}$ power-bounded (Wedhorn §8.1, eq. 8.1.1, p.73).
- $A$ is **strongly noetherian Tate** if $A\langle X_1, \ldots, X_n \rangle$ (the $n$-variable Tate algebra) is noetherian for every $n \ge 0$ (Wedhorn Prop & Def 6.36, p.54).

### 2.2. References

- **[Wedhorn]** Torsten Wedhorn. *Adic Spaces*. Lecture notes, arXiv:1910.05934v1, 14 October 2019. 107 pages. Citations of the form "Wedhorn X.Y" or "(Wedhorn p.N)" refer to the global numbering of this PDF.
- **[Hu1]** R. Huber. *Continuous valuations*. Math. Z. 212 (1993), 455–477.
- **[Hu2]** R. Huber. *A generalization of formal schemes and rigid analytic varieties*. Math. Z. 217 (1994), 513–551.
- **[Hu3]** R. Huber. *Étale cohomology of rigid analytic varieties and adic spaces*. Aspects of Mathematics E30, Vieweg & Sohn, Braunschweig, 1996. Cited by Wedhorn for the construction of $\mathcal{O}_X$ (3.7.1).
- **[BGR]** S. Bosch, U. Güntzer, R. Remmert. *Non-Archimedean Analysis*. Grundlehren 261, Springer, 1984. (Cited by Wedhorn Remark 6.37(2): completely valued field of height 1 is strongly noetherian, BGR §5.2.6 Theorem 1.)
- **[Stacks]** Stacks Project, https://stacks.math.columbia.edu. Tags referenced: 023N (descent for modules), 00MA (completion exactness for finite modules; **note**: NOT noetherianness of completion).
- **[Hübner]** Katharina Hübner. *Sheafiness of Huber's valuation spectrum* (preprint, arXiv:2405.06435). Cited for refinement-tree constructions.

### 2.3. State of the art

Wedhorn 8.28(b) is well-established mathematically (Huber 1994, BGR 5.2.6 chain). The Lean formalisation, to our knowledge, is the first attempt at this theorem.

---

## 3. Strategy

The proof follows Wedhorn pp.81–84 verbatim:

1. **Wedhorn Lemma 8.31** (p.82): $A$ noetherian complete Tate $\Rightarrow$ $A\langle X \rangle$ is faithfully flat over $A$, and $A\langle X \rangle/(f-X), A\langle X \rangle/(1-fX)$ are flat over $A$ for every $f \in A$.
2. **Wedhorn Prop 8.30** (p.82): $A$ strongly noeth Tate; $U \subseteq V \subseteq X$ rational $\Rightarrow$ $\mathcal{O}_X(V) \to \mathcal{O}_X(U)$ is flat.
3. **Wedhorn Cor 8.32** (p.83): $A$ strongly noeth Tate; finite rational cover $(U_i)$ $\Rightarrow$ $\mathcal{O}_X(X) \to \prod_i \mathcal{O}_X(U_i)$ is faithfully flat.
4. **Wedhorn Lemma 8.33** (p.83): $A$ complete strongly noeth Tate; $f \in A$ $\Rightarrow$ the augmented Čech complex of $\{R(f/1), R(1/f)\}$ is exact.
5. **Wedhorn Lemma 8.34** (p.84): $A$ complete strongly noeth Tate; $\mathcal{U}$ rational cover generated by $T \subseteq A$ with $T \cdot A = A$ $\Rightarrow$ $\mathcal{U}$ is $\mathcal{O}_X$-acyclic.
6. **Reduction**: Every open cover of $\mathrm{Spa}\, A$ has a refinement by a standard cover (Wedhorn Lemma 7.54 + Cor 7.53, both p.70); acyclicity transfers along refinement (Wedhorn Prop A.3). Gives Theorem 8.28(b).

The Lean architecture mirrors this. The sheaf-of-sets half — current target — requires only:
- **separation** = injectivity from "in particular injective" of 8.32,
- **gluing** = the $q=0$ content of 8.34.

The $q \ge 1$ cohomology vanishing requires the full Čech machinery (Wedhorn Appendix A), not in current target.

---

## 4. Project-specific definitions (Lean encoding, in mathematical form)

### 4.1. `RationalLocData`
A **rational localisation datum** is a tuple $(P, T, s)$ where $P = (A_0, I)$ is a pair of definition, $T \subseteq A$ finite, $s \in A$, plus the `hopen` condition: $\exists N$ such that for every $b \in I^N$, $b/s$ lies in $A_0[t/s : t \in T] \subseteq A_s$. Geometric content: "$R(T/s)$ is a well-defined rational subset of $\mathrm{Spa}(A, A^{+})$".

### 4.2. `presheafValue`
For $D = (P, T, s)$, $\mathrm{presheafValue}\, D$ is the completion of $A_s = A[s^{-1}]$ in the canonical $f$-adic topology of Wedhorn §8.1. Lean encoding of $A\langle T/s\rangle = \mathcal{O}_X(R(T/s))$.

### 4.3. `RationalCovering`
A tuple $(D_{\mathrm{base}}, (D_i)_i, \mathrm{hsubset}, \mathrm{hcover})$ where the $D_i$ are rational localisation data, each $R(T_i/s_i) \subseteq R(T_{\mathrm{base}}/s_{\mathrm{base}})$, and they jointly cover $R(T_{\mathrm{base}}/s_{\mathrm{base}})$. This is **more general** than Wedhorn's "rational cover generated by $T$ with $T \cdot A = A$" — it allows arbitrary finite rational covers of an arbitrary rational base.

### 4.4. `IsSheafy` (typeclass)
Encodes that for every rational covering $C$:
- (`embedding`) the product restriction $\mathrm{presheafValue}\, C_{\mathrm{base}} \to \prod_i \mathrm{presheafValue}\, C_i$ is a topological embedding;
- (`gluing`) compatible sections glue uniquely.

Sheaf-of-sets condition + topological control. Acyclicity in higher degrees NOT encoded.

### 4.5. `HasLocLiftPowerBounded` (typeclass)
Packages two ingredients used implicitly by Wedhorn: for $U \subseteq V$ rational, (a) the image of $s_V$ in $\mathcal{O}_X(U)$ is a unit; (b) lifted divisions $t_V/s_V$ are power-bounded in $\mathcal{O}_X(U)$. Both follow from Wedhorn 7.52(2) + 7.41 applied to $\mathcal{O}_X(U)$ (which is again strongly noeth Tate by Example 6.38).

### 4.6. `IsTateRing.principalPair`
For $A$ Tate, a **principal pair** is a pair of definition $(A_0, I)$ + a topologically nilpotent unit $\pi \in A_0$ of $A$ with $I = (\pi) \cdot A_0$. Constructed non-canonically (via choice) for every Tate ring.

### 4.7. `IsStronglyNoetherian` (typeclass)
$A\langle X_1, \ldots, X_n \rangle$ noetherian for every $n$.

---

## 5. Established (sorry-free) results

- **Discrete case** of `IsSheafy` (Wedhorn 8.28(c)).
- **Cor 8.32 abstract skeleton**: `productRestriction_faithfullyFlat_abstract` (given component flatness + Spec-surjectivity, concludes faithful flatness).
- **Stacks 023N descent equaliser** decomposed as K.1.a (cocycle map R-linear), K.1.b (R-image in kernel), K.1 (composition); K.1.c (the actual descent surjectivity) is a Cluster-I sorry below.
- **Lane C topological-inducing** for a single Laurent split, and inductive absorbing of additional pieces (~20 sorry-free lemmas, T273–T291 in the project's ticket vocabulary).
- **Wedhorn 8.30 flatness for Laurent-minus restrictions** via the project's `flat_over_base_tate_laurent` chain (Wedhorn 8.31(2) + Lemma 2.13 transport).
- **Refinement transfer**: `separation_of_finer_rational` and `gluing_of_finer_rational` (Wedhorn Prop A.3 analogues at the sheaf-of-sets level).

---

## 6. In progress — the IsSheafy target

```
isSheafy_ofStronglyNoetherianTate
  ├── derive (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
  │     └── via isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate   [SORRY — flagged FALSE]
  ├── derive hSpa (Spa-points above every prime)
  │     └── via exists_hSpa_points_global_of_stronglyNoetherianTate   [SORRY]
  ├── derive topo_inducing (productRestrictionSub is inducing)
  │     └── via productRestrictionSub_isInducing_tate   [SORRY]
  └── apply isSheafy_ofStronglyNoetherianTate_flat_of_topo_inducing
        ├── embedding ← rationalCovering_hasSeparation ∘ tateAcyclicity Part 1   [SORRY-blocked]
        └── gluing    ← rationalCovering_hasGluing    ∘ tateAcyclicity Part 2   [SORRY]
```

The `HasLocLiftPowerBounded A` instance required by `IsSheafy`'s typeclass declaration is derived from strongly-noeth Tate via Wedhorn Prop 7.52(2) + 7.41 (sorry-blocked).

---

## 7. The full transitive sorry inventory

Listed by mathematical cluster. Each entry gives: name, statement (Wedhorn-style English), claimed reference, audit verdict.

### Cluster A — Top-level IsSheafy main goals (3 sorries)

**A1. `isSheafy_ofStronglyNoetherianTate`** *(Wedhorn Thm 8.28(b), sheaf-of-sets half)*
> $A$ strongly noetherian Tate (with $[T_2]$, $[\mathrm{NonarchimedeanRing}]$ technical typeclasses) $\Rightarrow$ $\mathcal{O}_{\mathrm{Spa}(A,A^{+})}$ is `IsSheafy` (§4.4).

Verdict: **✓ matches Wedhorn 8.28(b)** at sheaf-of-sets level.

**A2. `isSheafy_ofStronglyNoetherianTate_flat`** *(variant with explicit principal pair)*
> Same conclusion as A1, taking $(P, [\mathrm{IsNoetherianRing}\, P.A_0], [\mathrm{IsDomain}\, A])$ as explicit parameters.

Verdict: **✓**.

**A3. `isSheafy_ofStronglyNoetherianTate_flat_of_topo_inducing`** *(variant taking hSpa + topo_inducing)*
> Same conclusion, takes the Spa-point witness and topological-inducing witness as hypotheses.

Verdict: **✓**.

### Cluster B — Direct dependencies of A1 (8 sorries)

**B1. `hasLocLiftPowerBounded_of_stronglyNoetherianTate`** *(instance, Wedhorn 7.52(2) + 7.41)*
> $A$ strongly noeth Tate $\Rightarrow$ for every $U \subseteq V$ rational, the image of $s_V$ in $\mathcal{O}_X(U)$ is a unit, and $t_V/s_V$ is power-bounded in $\mathcal{O}_X(U)$ for every $t \in T_V$.

Verdict: **✓** should follow from Wedhorn 7.41 + 7.52(2) applied to $\mathcal{O}_X(U)$ (again strongly noeth Tate by Example 6.38).

**B2. `isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate`** *(claim: Wedhorn 6.18 corollary)*
> $A$ strongly noetherian Tate $\Rightarrow$ the ring of definition $A_0$ of the canonical principal pair is noetherian.

Verdict: **⚠ FLAGGED FALSE.** Wedhorn proves only the converse (Remark 6.37(3)). Counterexample: $A = \mathbb{C}_p$ is strongly noeth Tate (Wedhorn Rem 6.37(2)), but the natural ring of definition $\mathbb{C}_p^{\circ}$ has non-finitely-generated maximal ideal (dense value group $\mathbb{Q}$). See §8.1.

**B3. `isNoetherianRing_A₀_of_stronglyNoetherianTate`** *(generic-pair version of B2)*
> $A$ strongly noeth Tate $\Rightarrow$ for ANY pair of definition $P$, the ring $P.A_0$ is noetherian.

Verdict: **⚠ FLAGGED FALSE** (same $\mathbb{C}_p$ counterexample).

**B4. `isStronglyNoetherian_of_isNoetherianRing_isTateRing`** *(claim: Wedhorn 6.18 forward implication)*
> $A$ noetherian Tate (with $[T_2]$, $[\mathrm{NonarchimedeanRing}]$) $\Rightarrow$ $A$ strongly noetherian Tate.

Verdict: **⚠ NOT IN WEDHORN / POSSIBLY OPEN.** Wedhorn proves this only for completely valued fields of height 1 (Remark 6.37(2), citing BGR §5.2.6). For general noetherian Tate rings, "noetherian $\Rightarrow A\langle X \rangle$ noetherian" is known to fail in adjacent settings (Nagata counterexamples for $A[[X]]$). See §8.2.

**B5. `exists_hSpa_points_global_of_stronglyNoetherianTate`** *(Wedhorn 7.45 chain)*
> $A$ strongly noeth Tate; finite $T \subseteq A$, $s \in A$, prime $\mathfrak{p}$ with $s \notin \mathfrak{p}$ $\Rightarrow$ $\exists v \in R(T/s)$ with $\mathfrak{p} \subseteq \mathrm{supp}(v)$.

Verdict: **✓ correct shape**. The non-open prime case needs Wedhorn Lemma 7.45 with noetherian ring of definition (blocked on B2/B3); open-prime case needs Wedhorn 7.51 trivial-valuation construction.

**B6. `productRestrictionSub_isInducing_tate`** *(Gap B, topological inducing)*
> For $A$ strongly noeth Tate and every rational covering $C$, the product restriction $\mathrm{presheafValue}\, C_{\mathrm{base}} \to \prod_i \mathrm{presheafValue}\, C_i$ is a topological inducing map.

Verdict: **✓ correct shape**. Discharge: Lane C single-step closer (done) + existence of Laurent refinement tree (P8, Cluster F).

**B7. `tateAcyclicity_separation_via_cor832`**
> $A$ strongly noeth Tate; $C$ rational covering; $x$ restricting to $0$ on every cover piece $\Rightarrow$ $x = 0$.

Verdict: **✓ matches Wedhorn 8.32 "in particular injective"**.

**B8. `tateAcyclicity_gluing_via_descent`** *(Wedhorn Lemma 8.34, gluing direction)*
> $A$ strongly noeth Tate; $C$ nonempty rational covering; compatible family $(f_i)$ $\Rightarrow$ $\exists$ global section.

Verdict: **✓ matches Wedhorn 8.34** at the $H^0=0$ level.

### Cluster C — Wedhorn-clean wrappers (5 sorries, all blocked on B2/B3)

**C1. `prop_8_30_flat_clean`** *(Wedhorn Prop 8.30)*
> $A$ strongly noeth Tate; $U \subseteq V$ rational $\Rightarrow$ $\mathcal{O}_X(V) \to \mathcal{O}_X(U)$ is flat.

Verdict: **✓ exact** match with Wedhorn 8.30.

**C2. `cor_8_32_clean`** *(Wedhorn Cor 8.32)*
> $A$ strongly noeth Tate; $C$ rational covering $\Rightarrow$ product restriction is faithfully flat.

Verdict: **✓ exact** match with Wedhorn 8.32.

**C3. `Spa_presheafValue_eq_rationalOpen`** *(Wedhorn Prop 8.2)*
> $A$ strongly noeth Tate; $D$ rational datum $\Rightarrow$ $\exists$ homeomorphism $\mathrm{Spa}(\mathrm{presheafValue}\, D, \cdot) \simeq R(D.T/D.s) \cap \mathrm{Spa}(A, A^{+})$.

Verdict: **✓ matches Wedhorn Prop 8.2**.

**C4. `presheafValue_isTateRing_clean`** *(Wedhorn Example 6.38)*
> $A$ strongly noeth Tate; $D$ rational datum $\Rightarrow$ $\mathrm{presheafValue}\, D$ is Tate.

Verdict: **✓ matches Wedhorn Ex 6.38**.

**C5. `presheafValue_isNoetherianRing_clean`** *(Wedhorn Example 6.38)*
> $A$ strongly noeth Tate; $D$ rational datum $\Rightarrow$ $\mathrm{presheafValue}\, D$ is noetherian.

Verdict: **✓ matches Wedhorn Ex 6.38**.

### Cluster D — Wedhorn 7.40–7.52 chain (15 sorries)

**D1. `exists_topNilp_ne_zero_of_analytic`** *(Wedhorn Rem 7.40(1), one direction, p.65)*
> $A$ Huber; $x \in \mathrm{Cont}(A)$ with non-open support $\Rightarrow$ $\exists a \in A^{\circ\circ}$ with $x(a) \ne 0$.

Verdict: **✓ exact**.

**D2. `rankOne_valueGroup_of_analytic`** *(Wedhorn Rem 7.40(5), p.65)*
> $A$ Huber; $x \in \mathrm{Cont}(A)$ analytic $\Rightarrow$ value group of $x$ admits order-monomorphism into $(\mathbb{R}_{>0}, \cdot)$.

Verdict: **✓ matches** 7.40(5) (microbial = rank 1) + Hahn's embedding theorem.

**D3. `mulArchimedean_of_rankOne_valueGroup`** *(elementary, closed this session)*
> Order-embedding into $\mathbb{R}_{>0}$ $\Rightarrow$ multiplicatively archimedean.

Verdict: **✓**.

**D4. `mulArchimedean_valueGroup_of_analytic`** *(composite of D2 + D3, closed)*

Verdict: **✓**.

**D5. `analytic_height_one_vle_one_on_powerBounded`** *(Wedhorn Prop 7.41, p.66)*
> $A$ Huber; $x \in \mathrm{Cont}(A)$ analytic; $a \in A^{\circ}$ $\Rightarrow$ $x(a) \le 1$.

Verdict: **✓ matches Wedhorn 7.41**. Lean drops explicit "height 1" hypothesis (follows from analyticity + continuity).

**D6. `locLift_divByS_isPowerBounded_of_tate`** *(algebraic-side, component of `HasLocLiftPowerBounded`)*
> Lift of $t_V/s_V$ to $\mathrm{Localization.Away}\, s_V$ is power-bounded in the algebraic-localisation topology.

Verdict: **✓ correct intermediate step**.

**D7. `locLift_divByS_isPowerBounded_completion_of_tate`** *(completion-side)*
> Same as D6 but in $\mathcal{O}_X(U) = \mathrm{presheafValue}\, U$.

Verdict: **✓ correct**, follows from D5 applied to $\mathcal{O}_X(U)$.

**D8. `wedhorn_7_42_powerBounded_iff_forall_continuous_vle_one`** *(claim: "Wedhorn 7.42")*
> $A$ complete Huber; $a \in A$ power-bounded $\iff$ $v(a) \le 1$ for every $v \in \mathrm{Cont}(A)$.

Verdict: **⚠ CITATION IMPRECISE**. Wedhorn Rem 7.42 (verbatim p.66) is about vertical generizations of $\Gamma_x$, not power-boundedness. The Lean statement combines D5 (Wedhorn 7.41) with a separate non-analytic argument; the combination is correct mathematically but not labelled "7.42" in Wedhorn. The correct combined reference is probably "7.41 + non-analytic argument via 7.40(5)" or possibly "Lemma 6.20 + 7.18 ingredient".

**D9. `exists_valuationSubring_dominating_for_rationalOpen`** *(Wedhorn 7.45 intermediate)*
> $A$ Huber, $\mathfrak{p}$ prime, $s \notin \mathfrak{p}$, $T$ finite $\Rightarrow$ $\exists$ valuation subring $B$ of $\mathrm{Frac}(A/\mathfrak{p})$ dominating images of $A_0$ and $t/s$ for $t \in T$, with $I \cdot A_0$ mapping into $B$'s non-units.

Verdict: **✓ standard Chevalley-style dominating-valuation construction**, backing Wedhorn 7.45's proof.

**D10. `exists_mem_rationalOpen_supp_ge_of_prime_noHArch`** *(Wedhorn Lemma 7.45 + lift)*
> $A$ complete Huber Tate with $[\mathrm{IsAdicComplete}\, P.I\, P.A_0]$; prime $\mathfrak{p}$, $s \notin \mathfrak{p}$, $T$ finite $\Rightarrow$ $\exists v \in R(T/s)$ with $\mathfrak{p} \subseteq \mathrm{supp}(v)$.

Verdict: **✓ matches Wedhorn 7.45** (non-open prime case).

**D11. `maxIdeal_isClosed_of_complete_huber`** *(Wedhorn Prop 7.51 part 1, p.69)*
> $A$ complete affinoid; $\mathfrak{m}$ maximal $\Rightarrow$ $\mathfrak{m}$ closed.

Verdict: **✓ exact**.

**D12. `exists_spa_point_supp_eq_maxIdeal_of_complete`** *(Wedhorn Prop 7.51 part 2, p.69)*
> $A$ complete affinoid; $\mathfrak{m}$ maximal $\Rightarrow$ $\exists v \in \mathrm{Spa}(A, A^{+})$ with $\mathrm{supp}(v) = \mathfrak{m}$.

Verdict: **✓ exact**.

**D13. `isUnit_iff_ne_zero_on_spa_of_complete`** *(Wedhorn Prop 7.52(2), p.70 — closed this session)*
> $A$ complete affinoid; $f$ unit $\iff$ $v(f) \ne 0$ for all $v \in \mathrm{Spa}(A, A^{+})$.

Verdict: **✓**.

**D14. `topologicallyNilpotent_eq_union_definitionIdeals`** *(used in Wedhorn 7.51 proof, p.69)*
> $A$ Huber; topologically nilpotent elements equal $\bigcup_P P.I$ over pairs of definition.

Verdict: **✓ standard**.

**D15. `units_eq_union_translates_of_oneAdd_topNilp`** *(Wedhorn 7.51 sub-step)*
> $A$ Huber: $A^{\times} = \bigcup_{u \in A^{\times}} u \cdot (1 + A^{\circ\circ})$.

Verdict: **⚠ FALSE without completeness.** Counterexample: $\mathbb{Z}$ with $p$-adic topology has $1+p \in 1 + A^{\circ\circ}$ but $1+p$ is not a unit in $\mathbb{Z}$. Lean signature lacks $[\mathrm{CompleteSpace}\, A]$.

**D16. `isOpen_units_of_complete_huber`** *(Wedhorn 7.51 sub-step, p.69)*
> $A$ complete affinoid $\Rightarrow$ $A^{\times}$ open in $A$.

Verdict: **✓ standard**.

### Cluster E — Wedhorn 6.18 chain (4 sorries)

**E1. `_sub_lemma_L3_1a_completion_fg_complete`** *(claim: BGR §3.7.2/1)*
> $A$ complete with countably-generated uniformity; $M$ finitely generated Hausdorff topological $A$-module $\Rightarrow$ $M$ complete.

Verdict: **⚠ FALSE.** BGR §3.7.2/1 actually requires the *completion* $\hat M$ to be finitely generated over $A$, not $M$. Counterexample: $A = \mathbb{Z}$ discrete, $M = \mathbb{Z}$ $p$-adic; $M$ is fg over $A$ but $\hat M = \mathbb{Z}_p \ne \mathbb{Z}$.

**E2. `wedhorn_6_18_unique`** *(Wedhorn Prop 6.18(1) uniqueness, p.49)*
> $A$ complete noeth Tate; $M$ finitely generated $A$-module $\Rightarrow$ $\exists!$ uniform structure $\tau$ on $M$ that is `IsUniformAddGroup` + complete + countably-generated.

Verdict: **⚠ FALSE as stated** without further constraints. Wedhorn's uniqueness implicitly assumes $\tau'$ is an $A$-module topology with continuous scalar action. Counterexample (project's b2_log): $M = \bigoplus_{\mathbb{N}} \mathbb{Z}/2$ with discrete uniformity vs. another non-discrete UAG uniformity.

**E3. `_sub_lemma_L5_1_2_adicCompletion_noetherian`** *(claim: Stacks 00MA)*
> $R$ noetherian commutative; $I \subseteq R$ ideal $\Rightarrow$ the $I$-adic completion $\hat R$ is noetherian.

Verdict: **✓ statement TRUE** (Atiyah-Macdonald 10.27; standard). **⚠ CITATION WRONG**: Stacks 00MA is "Lemma 10.97.1" about exactness of completion for short-exact sequences of finite modules. The correct Stacks tag for "completion of noetherian is noetherian" is closer to 0316 / 05GG.

**E4. `_sub_lemma_L5_1_3_inductive_step`** *(Hilbert-basis + 00MA chain)*
> $A$ complete Tate; $A\langle X_1, \ldots, X_k \rangle$ noetherian $\Rightarrow$ $A\langle X_1, \ldots, X_{k+1} \rangle$ noetherian.

Verdict: **✓ standard**, given E3.

### Cluster F — Refinement-to-standard-cover + Wedhorn Lemma 8.34 routing (12 sorries)

**F1. `exists_standard_cover_refining`** *(claim: from Wedhorn Lemma 7.54)*
> $A$ strongly noeth Tate; $C$ rational covering $\Rightarrow$ $\exists S \subseteq A$ finite with $\mathrm{Ideal.span}\, S = \top$, refining $C$ via the project's `refines_cover` / `refines_contain` / `refines_span_top` triple.

Verdict: project-internal `refines_*` triple, see F2 for the deeper concern.

**F2. `exists_ideal_generators_refining_cover`** *(claim: Wedhorn Lemma 7.54 directly, p.70)*
> $A$ strongly noeth Tate; $C$ rational covering $\Rightarrow$ $\exists S \subseteq A$ finite, $\mathrm{Ideal.span}\, S = \top$, such that:
> (a) every $v \in R(C_{\mathrm{base}})$ lies in some $R(S/f)$ for $f \in S$, AND
> (b) every $R(S/f)$ for $f \in S$ is contained in some $R(E.T/E.s)$ for $E \in C$.

Verdict: **⚠ POTENTIAL SCOPE ERROR.** By Wedhorn Cor 7.53 (p.70), $\{R(S/f) : f \in S\}$ covers ALL of $\mathrm{Spa}\, A$ when $\mathrm{Ideal.span}\, S = \top$. The required (b) then forces each $R(S/f) \subseteq R(C_{\mathrm{base}})$, hence $\bigcup_f R(S/f) \subseteq R(C_{\mathrm{base}})$. Combined with covering ALL of $\mathrm{Spa}\, A$, this forces $R(C_{\mathrm{base}}) = \mathrm{Spa}\, A$ (only the trivial base case). Wedhorn Lemma 7.54 is stated for covers of $\mathrm{Spa}\, A$, not relative to a sub-rational-open. See §8.3.

**F3. `exists_standard_cover_refining_via_754`** *(packaging of F2 in `refines_*` triple)*

Verdict: same scope concern as F2.

**F4. `exists_wedhorn_ratio_laurent_refinement_tree_realized`** *(P8, Wedhorn 8.34 tree)*
> $A$ strongly noeth Tate, $[\mathrm{IsDomain}\, A]$, $[\mathrm{DecidableEq}\, A]$, $(P, [\mathrm{IsNoetherianRing}\, P.A_0])$; $C$ rational covering $\Rightarrow$ $\exists$ a `RatioLaurentTree` $t$ and a `RatioTreeRealization` $\rho$ such that $\rho$ refines $C$ and every split of $t$ is topologically inducing.

Verdict: **✓ correct shape** for Wedhorn 8.34's "ratio Laurent tree" construction in steps (i)-(iv).

**F5. `exists_wedhorn_ratio_laurent_refinement_tree_realized_clean`** *(Wedhorn-exact form, no project extras)*

Verdict: **✓ correct shape**. Removes $[\mathrm{IsDomain}\, A]$ (Wedhorn doesn't use it).

**F6. `exists_wedhorn_laurent_refinement_tree`** *(legacy I.1, plain `LaurentTree` output)*

Verdict: **✓ correct shape**, kept for backward compat.

**F7. `exists_first_stage_laurent_tree_unit_generated`** *(P6/W2, Wedhorn 8.34 step (ii))*
> Strongly noeth Tate (+ technical hypotheses), $C$ + standard-cover $S$ $\Rightarrow$ $\exists$ a topologically nilpotent unit $s \in A^{\times}$ and a first-stage Laurent tree $t_{\mathrm{outer}}$ generated by $\{s^{-1} f : f \in S\}$, with each leaf having a unit-generated restricted cover.

Verdict: **✓ matches Wedhorn 8.34 step (ii)**, which uses Cor 7.32 to produce $s$.

**F8. `unitGeneratedCover_has_relative_ratioLaurentRefinement`** *(P5/W3, Wedhorn 8.34 step (iii))*
> A unit-generated cover in $\mathcal{O}_X(L)$ admits a Laurent refinement by ratios of the generating units.

Verdict: **✓ matches Wedhorn 8.34 step (iii)** at the relative level.

**F9. `relative_laurent_tree_to_absolute`** *(P4/W3-transport)*
> A relative Laurent tree in $\mathcal{O}_X(L)$ transports to an absolute Laurent tree in $A$ via rational-subdomain-stability transport.

Verdict: project-specific; matches Wedhorn's identifications.

**F10. `relative_ratio_split_transports_to_RatioNodeData`** *(P3, per-node transport)*
> A single relative ratio-split node transports to a `RatioNodeData`.

Verdict: project-specific.

**F11. `productRestrictionSub_isInducing_via_ratio_tree`** *(T-GapB.1, consumer of P8)*
> Given a `RatioLaurentTree` realisation $\rho$ refining $C$ with all-splits-inducing, $\mathrm{productRestrictionSub}\, C$ is topologically inducing.

Verdict: **✓ correct shape** — the "consume the refinement tree" step.

**F12. `tateAcyclicity` Part 2** *(LaurentRefinement-side gluing, blocked on import cycle)*
> Strongly noeth Tate, $(P, [\mathrm{IsNoetherianRing}\, P.A_0])$; nonempty rational cover with compatible family $\Rightarrow$ $\exists$ global section.

Verdict: **✓ matches Wedhorn 8.34's $H^0$ content**. The sorry exists because the upstream file cannot import the downstream Cor 8.32 + descent equaliser machinery.

### Cluster G — Restriction-map / localisation scaffolding (5 sorries)

**G1. `restrictionMapHom_surj`** *(claim retired: surjectivity of single restriction)*
> $A$ noeth Tate; $D \subseteq D_0$ rational $\Rightarrow$ $\mathrm{restrictionMapHom}\, D_0 \to D$ is surjective.

Verdict: **⚠ FALSE in general** (project flagged "intentionally over-strong"). The completed rational localisation $A\langle T'/s' \rangle$ does not have a single algebraic generator over $A\langle T/s \rangle$.

**G2. `restrictionMapHom_injective`** *(claim retired: injectivity of single restriction)*
> $A$ noeth Tate; $D \subseteq D_0$ rational $\Rightarrow$ $\mathrm{restrictionMapHom}\, D_0 \to D$ injective.

Verdict: **⚠ FALSE in general** (project-flagged FALSE; counterexample $A = k\langle T, U \rangle/(TU)$, $U = R(1/T)$).

**G3. `isClosed_setOf_mul_eq_zero`** *(general topology)*
> $R$ Hausdorff topological commutative ring; $\{(x,y) : xy = 0\}$ closed in $R \times R$.

Verdict: **✓ standard topology fact**.

**G4. = C4** (`presheafValue_isTateRing_clean`).

**G5. = C5** (`presheafValue_isNoetherianRing_clean`).

### Cluster H — Wedhorn 7.31, 7.32, 7.35 supporting lemmas (4 sorries)

**H1. `exists_zero_nbhd_lt_on_qc`** *(Wedhorn Lemma 7.31, p.63)*
> $A$ affinoid; $X \subseteq \mathrm{Spa}(A, A^{+})$ quasi-compact; $f \in A$ with $|f(x)| \ne 0$ for all $x \in X$ $\Rightarrow$ $\exists$ open neighborhood $I$ of $0 \in A$ with $|a(x)| < |f(x)|$ for all $a \in I$, $x \in X$.

Verdict: **✓ exact** match with Wedhorn 7.31.

**H2. `exists_dominating_unit_noHArch_finset`** *(finset form of Wedhorn Cor 7.32)*
> $A$ Tate affinoid; $T$ finite subset of $A$ with "$\forall v, \exists t \in T, v(t) \ne 0$" $\Rightarrow$ $\exists$ unit $s \in A^{\times}$ such that $\forall v \in \mathrm{Spa}(A, A^{+}), \exists t \in T, v(s) < v(t)$.

Verdict: **✓** — this is exactly the finset form Wedhorn uses in the proof of Lemma 8.34 step (ii) (p.84).

**H3. `Spa.proConstructible_in_SpvAI`** *(Wedhorn 7.35(1), p.64)*
> $A$ affinoid with pair of definition $P$ $\Rightarrow$ $\mathrm{Spa}(A, A^{+})$ is pro-constructible in $\mathrm{Spv}(A, I \cdot A)$.

Verdict: **✓ matches Wedhorn 7.35 proof**.

**H4. `isCompact_preimage_rationalOpen_noHArch`** *(Wedhorn 7.35(2), p.64)*
> $A$ Tate Huber + pair of definition $P$; $T \subseteq A$ finite, $s \in A$ $\Rightarrow$ preimage of $R(T/s)$ is compact.

Verdict: **✓ matches Wedhorn 7.35(2)**.

### Cluster I — Stacks 023N descent + Wedhorn 8.33 + misc (3 sorries)

**I1. `faithfullyFlat_cocycle_kernel_eq_algebraMap_range`** *(Stacks 023N specialised)*
> $R \to S$ faithfully flat; $s \in S$ with $1 \otimes s = s \otimes 1$ in $S \otimes_R S$ $\Rightarrow$ $\exists r \in R$ with $r \cdot 1_S = s$.

Verdict: **✓ matches Stacks 023N** specialised to the trivial descent datum on $S$ itself. Stacks fetched verbatim: "the descended module is characterized as $M = \{n \in N : 1 \otimes n = \varphi(n \otimes 1)\}$".

**I2. `laurentCover_exact_general`** *(Wedhorn Lemma 8.33, p.83 generalisation)*
> $A$ Huber, Tate, noetherian, complete, T2, NonarchimedeanRing; $f \in A$ $\Rightarrow$ the 4-tuple $(\epsilon\mathrm{-gen}\, f, \delta\mathrm{-gen}\, f)$ for the 2-element Laurent cover is exact.

Verdict: **✓ matches Wedhorn 8.33**, generalised away from $[\mathrm{IsDomain}]$ via Krull-intersection.

**I3. `iteratedPlus_forwardToCompletion_continuous` / `iteratedMinus_forwardToCompletion_continuous`** *(LaurentRefinement project-specific continuity)*
> Continuity of iterated plus/minus forward maps in the Laurent decomposition chain.

Verdict: project-specific scaffolding; natural continuity statements.

### Cluster K — Mis-located scaffolding (2 sorries)

**K1. `spa_point_nonOpen_of_rational_subset`** *(Wedhorn 7.45 + relative prime extension)*
> $A$ Huber; $D \subseteq D_0$ rational; prime $p$ with $s_{D_0} \in p$, $s_{D'} \notin p$, $p$ not open $\Rightarrow$ $\exists v \in R(D'.T/D'.s)$ with $p \subseteq \mathrm{supp}\, v$.

Verdict: project-internal corollary of 7.45. Docstring says "proof located downstream".

**K2. `restrictionMapAlg_continuous_of_huber_completion`** *(transport-of-power-bounded-generators continuity)*
> Continuity of algebraic-to-completion restriction lift, under power-boundedness on lifted generators.

Verdict: project-internal continuity scaffolding.

### Summary of audit

- **Mathematically problematic (FALSE or scope error)**: B2, B3, B4, D15, E1, E2, F2 (with F3 inheriting), G1, G2. *9 statements*.
- **Mathematically true but mis-cited**: E3 (Stacks 00MA actually about completion exactness, not noetherianness).
- **Citation imprecise but content correct**: D8 (combination of 7.41 + non-analytic, not Wedhorn's 7.42).
- **Verified correct against Wedhorn/Stacks**: 38 statements.
- **Project-internal scaffolding without direct Wedhorn analogue**: ~6 statements (B1, F9, F10, G3, I3, K1, K2).

---

## 8. Detailed treatment of the five headline concerns

### 8.1. The Wedhorn 6.18 chain (forward direction) is FALSE

`isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate` (B2) asserts:

> *(claim)* For $A$ strongly noetherian Tate, there exists a pair of definition $(A_0, I)$ with $A_0$ noetherian.

**Counterexample.** $A = \mathbb{C}_p$, the $p$-adic completion of $\overline{\mathbb{Q}_p}$.
- $A$ is a completely valued non-archimedean field of height 1.
- By Wedhorn Remark 6.37(2) (citing BGR §5.2.6 Theorem 1), $A$ is strongly noetherian Tate.
- The natural ring of definition is $A_0 = A^{\circ} = \{x \in \mathbb{C}_p : |x| \le 1\}$, with topologically nilpotent unit $\pi = p$.
- The maximal ideal $\mathfrak{m} = \{x : |x| < 1\}$ of $A^{\circ}$ is **NOT finitely generated** (the value group is $\mathbb{Q}$, dense in $\mathbb{R}_{>0}$).
- Hence $A^{\circ}$ is not noetherian.

The only Wedhorn-stated direction is **Remark 6.37(3)**: *noetherian ring of definition $\Rightarrow$ strongly noetherian Tate* (the converse).

`isNoetherianRing_A₀_of_stronglyNoetherianTate` (B3) is the generic-pair-of-definition version with the same counterexample.

### 8.2. Wedhorn 6.18 forward implication (B4) is OPEN

`isStronglyNoetherian_of_isNoetherianRing_isTateRing` (B4) asserts:

> *(claim)* $A$ noetherian Tate (with $[T_2]$ + $[\mathrm{NonarchimedeanRing}]$) $\Rightarrow$ $A$ strongly noetherian Tate.

Wedhorn proves this only for completely valued fields of height 1 (Remark 6.37(2)). For general noetherian commutative rings, the analogous power-series completion claim "$R$ noeth $\Rightarrow R[[X]]$ noeth" can fail (Nagata-type counterexamples in non-excellent rings). We don't see a proof of the Tate-algebra version in Wedhorn for general noetherian Tate base.

### 8.3. Wedhorn Lemma 7.54 lifting (F2) is type-misaligned

`exists_ideal_generators_refining_cover` (F2) asserts:

> *(claim)* For $A$ strongly noeth Tate, $C$ a rational covering of $R(C_{\mathrm{base}})$, there exist $S \subseteq A$ with $\mathrm{Ideal.span}\, S = \top$ AND each $R(S/f) \subseteq$ some cover piece $R(E.T/E.s)$.

By Wedhorn Cor 7.53 (p.70), $\{R(S/f) : f \in S\}$ covers ALL of $\mathrm{Spa}\, A$ when $S$ generates the unit ideal. The containment condition forces every $R(S/f) \subseteq R(C_{\mathrm{base}})$, hence $\mathrm{Spa}\, A = \bigcup R(S/f) \subseteq R(C_{\mathrm{base}}) \subsetneq \mathrm{Spa}\, A$, contradiction unless $R(C_{\mathrm{base}}) = \mathrm{Spa}\, A$ (trivial base).

Wedhorn Lemma 7.54 itself produces $f_i \in A$ for a cover of $\mathrm{Spa}\, A$. It does NOT directly give a refinement relative to a sub-rational-open.

**Natural fix:** apply Wedhorn 7.54 to the strongly noetherian Tate affinoid $\mathcal{O}_X(C_{\mathrm{base}})$ (Wedhorn Example 6.38 confirms it is again strongly noeth Tate), obtaining $f_i \in \mathcal{O}_X(C_{\mathrm{base}})$ — NOT $f_i \in A$. The signature would change accordingly.

### 8.4. B2-flagged statements lacking hypothesis

Three project-internal-flagged sorries with their own counterexamples:

- **D15** (`units_eq_union_translates_of_oneAdd_topNilp`): needs $[\mathrm{CompleteSpace}\, A]$ for the geometric-series unitisation $\frac{1}{1+n} = \sum (-n)^k$. Counterexample: $\mathbb{Z}$ $p$-adic, $1+p \in 1 + A^{\circ\circ}$ but $1+p$ not a unit in $\mathbb{Z}$.
- **E1** (`_sub_lemma_L3_1a_completion_fg_complete`): needs $\hat M$ fg over $A$, not $M$ fg over $A$.
- **E2** (`wedhorn_6_18_unique`): needs $[\mathrm{ContinuousSMul}]$ constraint on the alternative uniformity $\tau'$.

Each is in `b2_log.jsonl` with counterexample.

### 8.5. Wedhorn 8.28(b) acyclicity vs. our IsSheafy scope

Wedhorn 8.28(b) has TWO parts: (i) sheaf-of-complete-topological-rings; (ii) $H^q(U, \mathcal{O}_X) = 0$ for $q \ge 1$ on rational $U$. The Lean `IsSheafy` typeclass encodes only (i). Acyclicity (ii) requires Čech machinery from Wedhorn Appendix A, not yet developed in the project.

---

## 9. Open questions for the reviewer

**Q1 (highest priority, soundness on Wedhorn 6.18 chain).** Is the implication

> *$A$ strongly noetherian Tate $\Rightarrow$ $\exists$ noetherian ring of definition of $A$*

correct in any sensible generality, or is the $\mathbb{C}_p$ counterexample correct? If $\mathbb{C}_p$ is a genuine counterexample, what is the right statement of the analogue of Wedhorn Prop 6.18 (uniqueness of fg-module topology) without assuming a noetherian ring of definition exists? Does Wedhorn 8.28(b) still hold when $A$ is strongly noetherian Tate but has no noetherian ring of definition?

**Q2 (related: scope of B4).** Is "noetherian Tate $\Rightarrow$ strongly noetherian Tate" known in any generality beyond completely valued fields of height 1 (BGR §5.2.6 Theorem 1)? If it's open in general, what is the right setting for our project — restrict to "complete Tate with a noetherian ring of definition" everywhere?

**Q3 (Wedhorn 7.54 lifting).** For F2 / F3: do you confirm the analysis that $f_i$ must live in $\mathcal{O}_X(C_{\mathrm{base}})$ rather than in $A$? If so, the fix propagates through the entire P3–P8 chain backing the topological-inducing of `productRestrictionSub` (B6). Is there a slicker way to formulate this refinement than per-leaf transport via Wedhorn Example 6.38?

**Q4 (overall strategy).** Is the project's overall strategy — decomposing Wedhorn 8.28(b) into ~30 named sub-lemmas across 7 files, with most depending on the Wedhorn 6.18 chain (which is now known to be false in the assumed form) — structurally sound, or does it need fundamental restructuring? Specifically, would you recommend:
- (a) restating everything to take a noetherian ring of definition as an extra hypothesis (relinquishing the "Wedhorn-clean" no-extras formulation);
- (b) restricting to a less general setting (e.g., Tate algebras over a non-archimedean field of height 1, where BGR §5.2.6 applies);
- (c) keeping the architecture but accepting the "Wedhorn-clean" wrappers will never be discharged — only their parametric forms;
- (d) something else.

**Q5 (Čech infrastructure).** Can the sheaf-of-sets condition (existence + uniqueness of glueings) for arbitrary covers be derived just from (i) Wedhorn Cor 8.32 + (ii) Wedhorn 8.34 for standard covers + (iii) refinement transfer for sheaf conditions (NOT for cohomology) — i.e., without developing the full Čech cohomology machinery? Or does the project genuinely need Wedhorn Appendix A?

**Q6 (citation for E3).** What is the correct Stacks tag for "I-adic completion of noetherian ring is noetherian"? We currently cite Stacks 00MA, but verbatim Stacks 00MA is Lemma 10.97.1 about completion exactness — a different result.

**Q7 (citation for D8).** Where exactly in Wedhorn (or Huber) is the statement "$a \in A$ power-bounded $\iff v(a) \le 1$ for every $v \in \mathrm{Cont}(A)$" found? Wedhorn Rem 7.42 (p.66) is about vertical generizations of $\Gamma_x$, not power-boundedness. Have we mis-cited, or is there an intermediate result (e.g., Wedhorn 7.18 + an integrality argument) we're missing?

**Q8 (project-internal architecture).** The project has a `restrictionMap_isLocalization` lemma (claiming $\mathcal{O}_X(U)$ is the algebraic IsLocalization.Away of $\mathcal{O}_X(V)$ at the image of the denominator) and a separate `restrictionMap_flat_via_iteratedMinus` (Wedhorn-honest flatness via Lemma 8.31). The IsLocalization claim is acknowledged false in general (convergent denominator tails such as $\sum p^n X^{-n} \in \mathbb{Q}_p\langle X \rangle \langle T \rangle / (XT-1)$). Currently it compiles transitively because `restrictionMapHom_surj` (G1) is sorry-bodied. Is this a sound interim measure or should the false IsLocalization claim be removed outright, forcing the downstream Cor 8.32 chain to refactor through the Wedhorn-honest flatness path?

**Q9 (G1, G2: retired-as-false single-map lemmas).** Several downstream lemmas still transitively depend on the retired-as-false `restrictionMapHom_injective` / `restrictionMapHom_surj`. They compile only because the false lemmas have sorry bodies (which inhabit any type universally). Should the project's policy be:
- (a) Delete the false lemmas now and accept the downstream cascade of breakage, refactoring affected consumers immediately; or
- (b) Keep the sorry'd false lemmas as load-bearing scaffolding and migrate consumers gradually?

Currently the project does (b).

**Q10 (sanity check on F4–F11).** The Wedhorn 8.34 tree construction (P3–P8 chain) introduces project-specific concepts (`RatioLaurentTree`, `RatioTreeRealization`, "unit-generated cover", "relative ratio split", etc.) to encode Wedhorn's proof steps (i)-(iv). Do these encodings look natural / correct to you, or would you suggest restructuring? In particular: is the use of explicit data structures for the refinement tree the right move, or could it be done with a more abstract "exists a chain of refinements satisfying ..." statement?

---

## 10. Auxiliary established (sorry-free) results — for reference only

These do NOT need verification by the reviewer; included for context:

- `restrictionMap_flat_via_iteratedMinus`: Wedhorn 8.30 for Laurent-minus shape via Wedhorn 8.31 + 2.13 transport. Sorry-FREE.
- `productRestriction_faithfullyFlat_abstract`: abstract algebraic skeleton of Wedhorn Cor 8.32. Sorry-FREE.
- `faithfullyFlat_descent_equalizer`: Stacks 023N specialised to $N = S$, as equaliser of cocycle map. Sorry-FREE.
- `cor_8_32_clean_proof`: Cor 8.32 with explicit principal pair input. Sorry-FREE (delegates to canonical, which is sorry).
- Lane C single-step inducing: `productRestrictionSub` inducing for a single Laurent split (T273–T291). Sorry-FREE block of ~20 lemmas.
- `IsTateRing.exists_principal_pairOfDefinition`: every Tate ring has a principal pair. Sorry-FREE.
- `IsTateRing.spaIsAnalytic`: every $v \in \mathrm{Spa}\, A$ is analytic when $A$ is Tate (Wedhorn Prop 8.36). Sorry-FREE.

---

## 11. Document metadata

- **Project:** Lean 4 formalisation of Wedhorn's *Adic Spaces*, Tate-acyclicity / IsSheafy subproject.
- **Brief generated:** 2026-05-18.
- **Length:** ~14 pages, ~6500 words.
- **Build status:** project compiles with 162 `sorry`-warnings (≈55 are in the IsSheafy transitive closure described here).
- **Recent commit context:** closures of `wedhorn_7_52_2_isUnit_iff_forall_not_vle_zero`, `isUnit_iff_ne_zero_on_spa_of_complete`, `mulArchimedean_of_rankOne_valueGroup`, `isPowerBounded_of_discrete_presheafValue`, plus the K.1.a/b/(K.1) descent equaliser packaging. The four flagged statements in §8 were surfaced during a verbatim audit against Wedhorn arXiv:1910.05934v1 on 2026-05-18.

---

*End of brief.*
