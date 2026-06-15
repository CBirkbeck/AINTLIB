# Review brief — Tate acyclicity for strongly noetherian Tate rings

*Prepared 2026-05-11 for ChatGPT Pro (a senior generalist mathematician familiar with
adic spaces / Tate / rigid geometry). Picks up from the project's 2026-04-21 overview
packet. Self-contained: no repository access required.*

---

## 1. Goal

We are formalising in Lean 4 + Mathlib the sheaf property of the structure presheaf
on an adic spectrum for **strongly noetherian Tate** affinoid rings, i.e. the content
of Wedhorn's *Adic Spaces* Theorem 8.28(b). Concretely, for every finite rational
covering $\mathcal C = \{R(T_i/s_i)\}_i$ of the rational subset $R(T_0/s_0) \subseteq
\operatorname{Spa}(A, A^+)$, we want to show that the augmented complex

$$
0 \to \mathcal O_X\bigl(R(T_0/s_0)\bigr) \to \prod_i \mathcal O_X\bigl(R(T_i/s_i)\bigr)
   \to \prod_{i,j} \mathcal O_X\bigl(R(T_i/s_i) \cap R(T_j/s_j)\bigr)
$$

is exact, in the category of complete topological rings. This is the missing classical
input to define an *adic space* in the sense of Wedhorn 8.21 over the strongly
noetherian Tate class.

This brief is restricted to the Tate acyclicity work and the immediate surrounding
sheaf-theoretic infrastructure. We are **not** asking about perfectoid spaces,
tilting, or the wider formalisation.

---

## 2. Background and references

### 2.1 Setting and notation

We use Wedhorn's conventions throughout.

- $A$ is a Tate ring: a Huber ring with a *topologically nilpotent unit* $\pi \in A^\times$.
- $A^+ \subseteq A$ is a *ring of integral elements* (open, integrally closed in $A$,
  contained in the power-bounded subring $A^\circ$).
- $A_0 \subseteq A$ is a *ring of definition* (open, with an ideal of definition $I$
  such that the $I$-adic topology induces the topology of $A$). For Tate $A$ one
  may take $I = \pi A_0$.
- $\operatorname{Spa}(A, A^+) = \{v : A \to \Gamma \cup \{0\} \mid v\text{ continuous,
  }v(A^+) \leq 1\}/\sim$ — the adic spectrum.
- For $T \subseteq A$ finite and $s \in A$ with $T \cdot A = A$, the *rational subset*
  is $R(T/s) = \{v \in \operatorname{Spa}(A, A^+) \mid v(t) \leq v(s) \neq 0, \forall t \in T\}$.
- $A\langle X_1, \dots, X_n\rangle = \{\sum a_\alpha X^\alpha : a_\alpha \to 0\}$ —
  the Tate algebra (restricted power series). $A$ is *strongly noetherian* if
  $A\langle X_1, \dots, X_n\rangle$ is noetherian for all $n$.
- $\mathcal O_X\bigl(R(T/s)\bigr)$ — the structure presheaf value. Concretely it is the
  topological completion of the algebraic localisation $A[1/s]$ equipped with the
  *localisation topology* having $\{(\pi^n) \cdot A_0[T/s]\}_n$ as a 0-neighbourhood
  basis. In the project we denote this $\mathrm{presheafValue}\, D$, where
  $D = (P, T, s)$ packages a pair of definition $P = (A_0, I)$, the numerators $T$, and
  the denominator $s$.

### 2.2 Principal references

- [Wedhorn 2019] Torsten Wedhorn. *Adic Spaces*. Lecture notes, arXiv:1910.05934
  (cited as [W] below). The primary reference. We follow §6–§8.
- [Huber 1996] Roland Huber. *Étale cohomology of rigid analytic varieties and adic
  spaces*. Aspects of Mathematics E30. Vieweg, 1996. The original source for adic
  spectra.
- [Hübner 2024] Katharina Hübner. *On adic geometry over a non-noetherian base*.
  arXiv:2405.06435 (the version of the reduction we adapted for the geometric Lane C).
- [Zavyalov §2.3] Bogdan Zavyalov. *Quasicoherent sheaves on adic spaces*, §2.3 — used
  for the candidate-family / "Nullstellensatz refinement" geometric reduction.
- [Stacks 00MA] *The Stacks Project*, Tag `00MA`. Faithful flatness of the $I$-adic
  completion of a noetherian ring when $I \subseteq \operatorname{Jac}(R)$.
- [Conrad] Brian Conrad. *Several approaches to non-Archimedean geometry*. Used as a
  cross-check on rational subset arithmetic and Tate algebra completeness.

### 2.3 State of the art

Theorem 8.28(b) is a classical result going back to Huber [1996] in the published
proof and to Tate's original sheafiness theorem for rigid spaces (the case
$A$ a strongly noetherian $K$-affinoid algebra). The mathematics is settled; what is
new here is the **formalisation** in Lean 4. To our knowledge no comparable Lean
formalisation of Wedhorn 8.28(b) exists. Berkeley group work on perfectoid spaces (the
Buzzard–Commelin–Massot project) carried the sheaf condition as an axiom and did not
prove it.

---

## 3. Strategy

The current architecture (settled 2026-04-08 after an earlier "strict-exactness via
Banach open mapping" route was retired) follows Wedhorn's published proof on pp. 81–85
of [W]. The proof factors as four mathematical milestones, which the project organises
as **three working lanes** plus one common-base lane (Example 6.38):

1. **Common base (Example 6.38 in the Tate case).** Prove that for strongly
   noetherian Tate $A$ with rational data $D = (P, T, s)$, the presheaf value is a
   *topological* ring isomorphism
   $$
   \mathcal O_X\bigl(R(T/s)\bigr) \;\cong_{\mathrm{top}}\; A\langle X \rangle \;\bigl/\;
     (1 - s X),
   $$
   where the right-hand side carries the quotient of the canonical Tate topology on
   $A\langle X \rangle$ by the *closed* ideal $(1 - sX)$. Wedhorn's Prop. 6.17
   (ideals in noetherian Tate rings are closed) supplies the closedness; the universal
   property of completion gives the homeomorphism.

2. **Lane A — Laurent overlap (Example 6.39 / Lemma 8.33).** For $f \in A$ the
   *two-element Laurent cover* of $R(T_0/s_0)$ at $f$ is
   $\{R(\{f\} \cup T_0 / s_0), R(\{s_0\} / s_0 f)\}$ (the "$|f| \leq 1$" and
   "$|f| \geq 1$" halves). The acyclicity of the augmented Čech complex of this cover
   reduces to a $3 \times 3$ diagram chase on Tate-algebra quotients. The algebraic
   core (denoted $\mathrm{row3\_exact}$ in the project) is proved unconditionally.
   The *topological* lift to presheaf values requires identifying the overlap
   presheaf with a *bivariate* quotient — Example 6.39:
   $$
   \mathcal O_X\bigl(R(\{f, s_0/f\} / s_0)\bigr) \;\cong\;
       A\langle X, Y \rangle \;\bigl/\; (f - X, \, 1 - f Y).
   $$
   This is the "Laurent overlap bridge".

3. **Lane B — Cor 8.32 (faithful flatness of the product restriction).** Wedhorn's
   Cor. 8.32 says the product map
   $\mathcal O_X(R(T_0/s_0)) \to \prod_i \mathcal O_X(R(T_i/s_i))$ is *faithfully flat*
   for any rational cover, and hence in particular injective — this gives sheaf
   separation. The route uses Lemma 8.31 (flatness of $A\langle X\rangle$ and its
   quotients) and a Spa-point argument supplying the surjectivity-on-$\operatorname{Spec}$.

4. **Lane C — Wedhorn Lemma 8.34 / Hübner Lemma 3.8 (geometric reduction).** Any
   finite rational cover refines to a *standard cover* — a finite set $S \subseteq A$
   with $S \cdot A = A$, where the refinement pieces are *plus-pieces*
   $R(\{f\} \cup T_0 / s_0)$ for $f \in S$. Acyclicity then propagates by an outer
   induction on $|S|$ via iterated Laurent splits, each step closed by Lane A and Lane B.

The intended composition: **Lane C + Lane A + Lane B** assemble into the full
Theorem 8.28(b) gluing statement; the common-base Example 6.38 supplies the
identifications that make Lane A and Lane B usable at the presheaf level.

---

## 4. Definitions (project-specific data)

The Lean development packages Wedhorn's data slightly differently than the textbook;
we restate the project's conventions for the reviewer.

**Definition 4.1 (rational localisation datum).** A *rational localisation datum*
$D = (P, T, s)$ over a Huber ring $A$ consists of:
- a pair of definition $P = (A_0, I)$ for $A$,
- a finite subset $T \subseteq A$,
- an element $s \in A$ such that
- the rational subset $R(T/s) = \{v \in \operatorname{Spa}(A, A^+) : v(t) \leq v(s)
  \neq 0\ \forall t \in T\}$ is open *and* $A_0[T/s] \subseteq A[1/s]$ is well-defined.

**Definition 4.2 (presheaf value).** Given a datum $D$, the *presheaf value*
$\mathcal O_X(D)$ is the completion of $A[1/s]$ for the *localisation topology*
having $\{(\pi^n) \cdot A_0[T/s]\}_n$ as a $0$-neighbourhood basis. Equivalently
(Wedhorn 5.51), it is the universal complete topological ring receiving $A$ such
that $s$ becomes a unit and each $t/s$ is power-bounded.

**Definition 4.3 (rational covering).** A *rational covering* $\mathcal C$ of
$\mathcal O_X(D_0)$ is a finite family $(D_i)_{i \in I}$ of rational data, each
contained in $D_0$ (the inclusion of rational subsets in $\operatorname{Spa}(A, A^+)$),
such that every point of $R(T_0/s_0)$ lies in some $R(T_i/s_i)$.

**Definition 4.4 (sheafy).** $A$ is *sheafy* if for every rational covering
$\mathcal C$ of every rational $D_0$ in $\operatorname{Spa}(A, A^+)$, the product
restriction map
$$
\mathrm{restr}_{\mathcal C} : \mathcal O_X(D_0) \;\to\; \prod_i \mathcal O_X(D_i)
$$
is a *topological embedding* whose image equals the equaliser of the pair of
restrictions to $\prod_{i,j} \mathcal O_X(D_i \cap D_j)$. We split this into
*separation* (injectivity of $\mathrm{restr}_{\mathcal C}$) and *gluing*
(surjectivity onto the equaliser).

**Definition 4.5 (Laurent plus / minus datum).** For $f \in A$, the *plus datum*
at $f$ relative to $D_0$ is
$D_0^+(f) := (P, T_0 \cup \{f\}, s_0)$ (the "$v(f) \leq v(s_0)$" half), and the
*minus datum* is $D_0^-(f) := (P, \{s_0\}, s_0 \cdot f)$ (the "$v(f) \geq v(s_0)$"
half). The pair $\{D_0^+(f), D_0^-(f)\}$ is the *Laurent cover at $f$*.

**Definition 4.6 (standard cover / refinement).** A finite $S \subseteq A$ is a
*standard cover* of $D_0$ if $S \cdot A = A$ (equivalently, no common Spa-zero) and
each plus-piece $D_0^+(f)$ for $f \in S$ is contained in some target $D_i$ of the
original cover. The geometric reduction (Wedhorn 8.34) asserts every rational cover
admits such an $S$.

**Definition 4.7 (per-$E$ local covering).** Given an original cover $\mathcal C$
with target pieces $E \in \mathcal C$ and a standard cover $S$ refining $\mathcal C$,
the *per-$E$ local covering* at split point $f_0 \in A$ is the rational covering
of $E$ whose pieces are the Laurent plus-pieces and minus-pieces at $f_0$ of those
$D_0^+(f)$ ($f \in S$) that land inside $E$.

---

## 5. Established mathematical results

This section lists the substantive theorems already proved unconditionally
(no `sorry`, no project-specific axioms beyond Mathlib's). They are the algebraic
foundation on which the remaining lanes build.

### 5.1 Common-base infrastructure (Example 6.38, partial)

- **Theorem 5.1 (Algebraic Example 6.38).** *The algebraic localisation $A[1/s]$
  fits into a ring isomorphism $A[1/s] \cong A[X]/(1 - sX)$. After completion in the
  appropriate topologies, this lifts to a (continuous) ring map
  $A\langle X\rangle/(1 - sX) \to \mathcal O_X(D)$ with dense image.*
  *Sketch.* The algebraic iso is standard. The Tate algebra $A\langle X\rangle$
  surjects onto $\mathcal O_X(D)$ by evaluating $X \mapsto 1/s$; the kernel is
  $(1 - sX)$. Continuity uses the natural Tate topology on $A\langle X\rangle$
  matching the localisation topology under quotient. ∎

- **Open: Theorem 5.2 (topological Example 6.38).** *The map of Theorem 5.1 is a
  topological ring **isomorphism** in the strongly noetherian Tate case.*
  Status: algebraic content done; the homeomorphism uses Wedhorn Prop 6.17 (closed
  ideals) for the inverse and the Banach open mapping theorem. **Partially done**:
  the closed-ideal step is proved sorry-free for the principal-pair case;
  closing the homeomorphism for arbitrary noetherian Tate is in progress.

### 5.2 Algebraic Laurent acyclicity (Lemma 8.33 core)

- **Theorem 5.3 ($3\times 3$ row exactness, $\mathrm{row3\_exact}$).** *For any
  commutative ring $B$ and any $g \in B$, the sequence
  $$
  0 \to B \xrightarrow{\varepsilon} B\langle X\rangle/(g - X) \times
        B\langle X\rangle/(1 - gX) \xrightarrow{\delta} B\langle X, X^{-1}\rangle/(g - X) \to 0
  $$
  is exact in the category of $B$-modules, where $\varepsilon$ is the diagonal of
  the canonical maps and $\delta$ is the signed difference.*
  *Sketch.* A direct diagram chase. Surjectivity of $\delta$ uses the partial-sums
  decomposition of a Laurent polynomial into positive and negative parts.
  Exactness at the middle follows by polynomial division. The argument is
  completely elementary and does **not** require $B$ to be a domain or noetherian. ∎

- **Theorem 5.4 (Flatness, Wedhorn Lemma 8.31).** *For strongly noetherian Tate $A$
  and any $f \in A$, the rings $A\langle X\rangle$, $A\langle X\rangle/(f - X)$, and
  $A\langle X\rangle/(1 - fX)$ are flat over $A$.*
  *Sketch.* $A\langle X\rangle$ is the completion of $A[X]$ at the topology induced
  by an ideal of definition of $A$; flatness of completions of polynomial rings
  is classical. Flatness of the quotients uses regularity of $f - X$ and
  $1 - fX$ on $A\langle X\rangle$ (Wedhorn Lemma 8.30). ∎

### 5.3 Lane A — Laurent overlap (Example 6.39): algebraic core

- **Theorem 5.5 (Step B, $\mathrm{bivariateOverlap\_equiv\_B_{12,gen}}$).** *For any
  commutative ring $B$ and $b \in B$, there is a canonical ring isomorphism*
  $$
  B\langle X, Y\rangle / (b - X,\; 1 - bY) \;\cong\; B\langle X, X^{-1}\rangle / (b - X).
  $$
  *Sketch.* Modulo $(b - X)$, the relation $1 - bY$ becomes $1 - XY$, so $Y$ is
  forced to be the inverse of $X$. Conversely, in $B\langle X, X^{-1}\rangle/(b - X)$
  the element $X^{-1}$ satisfies $1 - bX^{-1} = 0$ modulo $(b - X)$, giving the
  inverse map. Both maps are checked on generators and the relations close up. ∎

- **Theorem 5.6 (forward Step A, $\mathrm{example638Bivariate\_forwardHom}$).**
  *There is a canonical continuous ring map $A\langle X, Y\rangle /(f - X, 1 - fY)
  \to \mathcal O_X(R(\{f, s_0/f\}/s_0))$ sending $X \mapsto f/1$ and
  $Y \mapsto 1/f$, factoring the bivariate evaluation through the quotient.*
  *Sketch.* The kernel of bivariate evaluation contains the relations by direct
  computation; the universal property of the quotient delivers the factorisation.
  Continuity comes from continuity of the bivariate evaluation. ∎

- **Theorem 5.7 (one round trip, $\mathrm{TA\_B_{1,gen}\_quotient\_forward\_backward\_eq\_id}$).**
  *The composition (forward bridge) ∘ (backward bridge) is the identity on
  $A\langle X\rangle /(f - X)$ taken as the quotient ring $B_{1,\mathrm{gen}}(f)$,
  modulo the outer Laurent overlap ideal.*
  *Sketch.* A direct generator check: the maps act on $X$ and $Y$ in compatible ways
  and the round trip preserves each. ∎

### 5.4 Lane B — Cor 8.32 infrastructure

- **Theorem 5.8 (generic Stacks 00MA, $\mathrm{AdicCompletion.faithfullyFlat\_of\_le\_jacobson\_bot}$).**
  *Let $R$ be a noetherian ring and $I \subseteq R$ an ideal contained in
  $\operatorname{Jac}(R)$. Then the natural map $R \to \widehat{R}_I$ to the
  $I$-adic completion is faithfully flat.*
  *Sketch.* Flatness is classical. For faithful flatness one shows that no maximal
  ideal of $\widehat R_I$ contracts to a non-maximal of $R$: a candidate maximal
  $\mathfrak m$ with $\mathfrak m \cdot R = R$ forces the contraction to miss $I$
  by Jacobson, and the level-1 evaluation $\widehat R_I \to R/I$ then contradicts
  proper-ness of $\mathfrak m$. ∎

- **Theorem 5.9 (Cor 8.32, product form, $\mathrm{productRestriction\_faithfullyFlat\_abstract}$).**
  *Suppose $\mathcal C = (D_i)$ is a rational cover of $D_0$ such that each
  individual restriction map $\mathcal O_X(D_0) \to \mathcal O_X(D_i)$ is flat and
  the Spa-points of $D_0$ lift to Spa-points of some $D_i$ (i.e., $\operatorname{Spec}$
  of the product $\prod_i \mathcal O_X(D_i)$ surjects onto $\operatorname{Spec}
  \mathcal O_X(D_0)$). Then the product restriction is faithfully flat, hence
  injective.*
  *Sketch.* Faithful flatness from componentwise flatness plus the surjective spec
  hypothesis is standard (cf. Stacks 02JT). Injectivity follows since faithful
  flatness implies pure injectivity in particular for ring maps. ∎

### 5.5 Lane C — geometric reduction infrastructure

- **Theorem 5.10 ($\mathrm{tateAcyclicity\_gluing\_via\_refinement\_cover\_level}$).**
  *Let $\mathcal C$ be a rational covering and let $\mathcal V$ be a refinement
  with a chosen target map $\tau : \mathcal V \to \mathcal C$ (each $V \in \mathcal V$
  contained in $\tau(V) \in \mathcal C$). If $\tau$ is surjective, $\mathcal V$
  satisfies gluing, and for each $E \in \mathcal C$ the $\mathcal V$-pieces refining
  $E$ separate sections on $E$, then $\mathcal C$ satisfies gluing.*
  *Sketch.* Push the compatible system on $\mathcal C$ down to $\mathcal V$ via
  $\tau$, glue on $\mathcal V$, and lift back using the per-$E$ separation to
  identify the lifted section's restriction to each $E$. ∎

- **Theorem 5.11 (per-$E$ local covering construction).** *Given a standard cover
  $S$ refining $\mathcal C$ with per-$E$ assignment $\rho_S : S \to \mathcal C$
  and a split point $f_0 \in A$, for each $E \in \mathcal C$ there is a canonical
  rational covering of $E$ — the **per-$E$ local covering** at $f_0$ — whose
  pieces are the Laurent halves of those $D_0^+(f)$ ($f \in S$, $\rho_S(f) = E$)
  at split point $f_0$.*
  *Status:* Constructed; nonempty when $E$ has a Spa-point. **Axiom-clean.**

- **Theorem 5.12 (direct per-$E$ Part-2 assembly).** *Assuming
  (a) the per-$E$ local covering separates sections (one application of
  Cor 8.32 per $E$), (b) the Laurent-cover gluing at the split point $f_0$ holds
  on each plus/minus half, and (c) the compatibility of the original system,
  the geometric reduction outputs a global section on $D_0$.*
  *Status:* Proved axiom-clean modulo the three suppliers above (no internal
  $\tau / \mathrm{Classical.choose}$ bridges remaining).

---

## 6. Work in progress

The acyclicity proof currently rests on three concurrent work streams, each
identified by mathematical name (the project tracks them via tickets, included
in §6a for cross-reference).

### 6.1 Lane A residual — quotient-Tate density

**Working on: reverse round trip of the Laurent overlap bridge (ticket
`TA_B1gen_quotient_specialized_equiv`).** Status: forward map, backward map, and
one round trip (Theorem 5.7) all done. The reverse round trip
$\mathrm{forward} \circ \mathrm{backward} = \mathrm{id}$
on $A\langle X, Y\rangle / (f - X, 1 - f Y)$ is the **single remaining algebraic
content** in Lane A. It reduces to one mathematical statement:

> **Density hypothesis.** *Let $B = A\langle X\rangle/(f - X)$ (the "$B_{1,\mathrm{gen}}$"
> quotient of $A$ by the principal Laurent plus-relation at $f$). Then every element
> of the Tate algebra $B\langle Z\rangle$ can be uniformly approximated, in the
> canonical Tate topology on $B\langle Z\rangle$, by polynomials in $B[Z]$.*

The obstruction is that $B = A\langle X\rangle/(f - X)$ is not directly known to
carry an instance of "Tate ring" in the formal sense — the project does not yet have
a pair of definition for the quotient. Once one is provided (or the density statement
is given more concretely from explicit truncation estimates), the round trip closes
and the bridge $A\langle X, Y\rangle/(f - X, 1 - fY) \cong B\langle Z, Z^{-1}\rangle/(f - Z)$
becomes an equivalence.

Depends on: nothing further. Blocks: Lane A finish; via Lane A, the Laurent
gluing supplier for Lane C.

### 6.2 Lane C residual — Zavyalov §2.3 C1 candidate-family construction

**Working on: Wedhorn 8.34 / Hübner 3.8 explicit refinement
(ticket `refines_by_standard_cover_per_E`).** Status: the strengthened
*per-$E$* refinement predicate is what Lane C consumes:

> *For every $E \in \mathcal C$ and every Spa-point $v$ of $R(T_E/s_E)$, there
> exists $f \in S$ such that $v$ lies in the plus-piece $D_0^+(f)$ **and** that
> entire plus-piece is contained in $R(T_E/s_E)$, with $S \cdot A = A$.*

The pointwise existence at one $v$ (the "C1" piece) requires Cor 7.32 of [W] (the
"dominating unit" lemma) applied to a suitable test family of denominators. The
recent commit stream T197–T212 has been building the algebraic infrastructure for
this — the "σ-clearing" suppliers that transfer a Cor 7.32 dominating unit
$\sigma \in (\mathrm{Localization.Away}\,s)^\times$ back to an element $\sigma' \cdot s^n
\in A$ usable as the witness $f$. The composition of these into a single
candidate-family supplier is open.

A separate packet (cf. the Zavyalov §2.3 packet circulated 2026-04-29) has asked
the reviewer for the precise candidate formula. Two natural sketches have been tried
and both fail:
- per-piece unit-rescaling $f_{E,i} = \sigma_E^{-1} t_{E,i}$ gives uniform domination
  of $\sigma_E$ but not subset-containment of the *individual* plus-piece;
- product-of-ratios $f_E = (\prod t_{E,i}) \cdot \sigma \cdot s_0^N$ fails because
  $v(\prod t) \leq v(s_0)$ does not give $v(t_i) \leq v(s_0)$ for each $i$.

Depends on: σ-clearing supplier composition (in progress). Blocks: Lane C closure.

### 6.3 Common-base topological Example 6.38

**Working on: presheaf value as a topological Tate-algebra quotient
(ticket `presheafValueTateQuotientEquiv_topological`).** Status: the algebraic ring
isomorphism is proved and the *forward* continuity ($A\langle X\rangle / (1 - sX) \to
\mathcal O_X(D)$ continuous) is proved. The remaining content is the reverse
continuity — equivalently, that the algebraic iso is *open* — which by the Banach
open mapping theorem (Wedhorn 6.16) follows once both rings are shown to be complete
metrisable. The quotient side requires the Tate topology on the **full** Tate algebra
$A\langle X\rangle$ (not just on its pair subring $A_0\langle X\rangle$); this is
landed for the principal pair and pending for arbitrary pairs.

Depends on: nothing further. Used by: Lane A (to lift the algebraic overlap iso to
a presheaf-level iso) and Lane B (to interpret presheaf-level flatness as
Tate-algebra-quotient flatness).

### 6.4 Single-map injectivity — RETIRED, see Counterexample 8.4

The original architecture relied on a theorem stating that each individual restriction
map $\mathcal O_X(D_0) \to \mathcal O_X(D_i)$ is injective. This was disproved in
2026-04-03 (Conrad counterexample); the full statement is in §8.4 below. Some
downstream gluing wrappers still reference the retired statement; they need to
be rerouted to the cover-level (product) injectivity of Cor 8.32, which is correct
and proven (Theorem 5.9).

### 6a. Ticket board (mathematical names only)

| Ticket (math name) | Statement | Status | Depends on |
|---|---|---|---|
| `row3_exact` | algebraic $3\times 3$ exactness of the Laurent diagram | done | – |
| `tateAlgebra_flat` | $A\langle X\rangle$ flat over $A$ | done | – |
| `flat_quotient_oneSubfX_general` | $A\langle X\rangle/(1-fX)$ flat over $A$ | done | – |
| `bivariateOverlap_equiv_B12gen` | Step B of Example 6.39 algebraic | done | – |
| `TA_B1gen_quotient_specialized_equiv` | full Example 6.39 ring iso | in progress (reverse round trip) | density on $B\langle Z\rangle$ |
| `presheafValueTateQuotientEquiv_topological` | Example 6.38 as **topological** iso | in progress (homeomorphism direction) | full Tate topology on $A\langle X\rangle$ |
| `AdicCompletion.faithfullyFlat_of_le_jacobson_bot` | generic Stacks 00MA | done | – |
| `productRestriction_faithfullyFlat_abstract` | Cor 8.32 abstract product form | done (conditional on spec surjectivity) | – |
| `refines_by_standard_cover_per_E` | Wedhorn 8.34 / Hübner 3.8 explicit refinement | in progress | Zavyalov §2.3 candidate formula |
| `tateAcyclicity_gluing_via_refinement_cover_level` | cover-level reduction theorem | done | – |
| `tateAcyclicity_Part2_direct_per_E` | per-$E$ Part 2 assembly | done | suppliers from Lane A & B |
| `tateAcyclicity` Part 1 (separation) | injectivity of $\mathrm{restr}_{\mathcal C}$ | open | Cor 8.32 at $\mathcal C$ |
| `tateAcyclicity` Part 2 (gluing) | gluing on $\mathcal C$ | open | Lane A + Lane C |
| `restrictionMapHom_injective` (single-map) | **FALSE** | retired (Conrad counterexample) | – |
| `locIdeal_le_jacobson_bot_unconditional` | unconditional Jacobson hypothesis | **FALSE** | – |

---

## 7. Targets (not yet attempted)

Once the three in-progress streams in §6 close, the assembly into the final
$\mathrm{tateAcyclicity}$ theorem is purely combinatorial:

- Compose Lane C (refinement to standard cover) with Lane A (Laurent cover gluing
  at each split point) and Lane B (per-$E$ separation) via the already-proved direct
  per-$E$ Part-2 assembly (Theorem 5.12).
- Promote the resulting gluing + separation pair to an `IsSheafy` instance for
  strongly noetherian Tate rings.
- The topological embedding part of `IsSheafy` (separation as a *topological*
  embedding, not just injection) requires the topological Example 6.38 lift to
  push through the algebraic embedding from Cor 8.32. This is the only post-assembly
  mathematical content.

---

## 8. Where we're stuck

This is the heart of the brief. We list three blockers, in roughly decreasing
priority.

### 8.1 Lane A reverse round trip — quotient-Tate density

The single remaining algebraic content in Lane A is:

> **Open lemma 8.1.** *Let $A$ be a strongly noetherian Tate ring and $f \in A$
> non-unit (or arbitrary). Let $B = A\langle X\rangle / (f - X)$ with the quotient
> topology of the canonical Tate topology on $A\langle X\rangle$. Then $B$ is a
> Tate ring and the polynomials $B[Z] \subseteq B\langle Z\rangle$ are dense in the
> canonical Tate topology on $B\langle Z\rangle$.*

What we have tried:
- Stating the density directly via the Tate-algebra coefficient bound: every
  element $\sum_n b_n Z^n \in B\langle Z\rangle$ is the limit of its truncations
  $\sum_{n \leq N} b_n Z^n$ because the coefficient sequence tends to $0$ in $B$.
  This is *true* mathematically, but in Lean it requires the **instance**
  $\mathrm{IsTateRing}\,B$, which is what we don't yet have.
- Trying to construct a pair of definition on $B$ directly: take the image of
  $A_0\langle X\rangle$, an ideal generated by the image of $\pi$. Open in $B$,
  $\pi$ becomes nilpotent of order $\geq 1$ on each coefficient. The mathematics
  appears to work; the obstruction is bookkeeping (showing the image is an honest
  subring with the expected Huber-pair properties).
- Side-stepping density entirely: refactor the round trip to use only universal
  properties so density never appears. This would require giving the quotient
  a universal characterisation as "the universal Tate ring under $A\langle X\rangle$
  killing $(f - X)$", but it's unclear whether that's strictly stronger or weaker
  than density.

**The question is whether we should pursue (a) the direct pair-of-definition
construction on $B$ (mostly bookkeeping), (b) a specialised density lemma that
bypasses Tate-ring instances, or (c) a more abstract reformulation that makes
density unnecessary.**

### 8.2 Lane C — Zavyalov §2.3 candidate-family C1

The required statement is:

> **Open lemma 8.2.** *For every rational cover $\mathcal C = (D_i)$ of $D_0$
> over strongly noetherian Tate $A$, every $E \in \mathcal C$, and every Spa-point
> $v \in R(T_E/s_E)$, there exists $f \in A$ such that the plus-piece
> $D_0^+(f) = R(T_0 \cup \{f\}/s_0)$ contains $v$ and is contained in $R(T_E/s_E)$.
> Moreover, the collection of such $f$'s (ranging over all $E, v$) can be chosen
> finite and generating the unit ideal in $A$.*

The Zavyalov §2.3 / Wedhorn 8.34 / Hübner 3.8 proofs all describe $f$ as a *ratio
cleared by a dominating unit*, but the precise formula has been hard to extract
from the literature. The candidate sketches (per-piece $\sigma_E^{-1} t_{E,i}$,
product-of-ratios $\prod t \cdot \sigma \cdot s_0^N$) both fail to satisfy
*containment of the individual plus-piece in $E$*; they satisfy weaker properties
like "joint intersection ⊆ $E$" or "uniform domination at every Spa-point", neither
of which is what `refines_cover_per_E` consumes.

A separate packet (the Zavyalov C1 packet, 2026-04-29) was prepared and asks
the reviewer for the precise formula; it has not yet been answered.

**The question is whether (a) the precise candidate is something more delicate than
the natural ratios — perhaps involving multiple powers and a careful interlocking
of denominators across $E$'s — or (b) the "single $f$ per Spa-point" shape of
`refines_cover_per_E` should be replaced by a "finite family $F_v$" shape, which
would require revising Lane C's outer induction.**

### 8.3 Lane B — the unconditional Jacobson route is false

The Lane B route initially aimed to close Cor 8.32 unconditionally by showing
that for any rational localisation datum $D = (P, T, s)$, the relation

> $\mathrm{locIdeal} \subseteq \operatorname{Jac}(0)$ in $\mathrm{locSubring} = A_0[T/s]$

holds; combined with Theorem 5.8 this would give faithful flatness of
$\mathrm{locSubring} \to \mathcal O_X(D)$ for free, and Cor 8.32 would follow.

This is **mathematically false in general**. Concrete counterexample:

> **Counterexample 8.3.** Let $A = \mathbb Q_p\langle X\rangle$, $A_0 = \mathbb Z_p
> \langle X\rangle$, $\pi = p$, $I = (p)$. Take $T = \{X\}$, $s = p$. Then
> $\mathrm{locSubring} = \mathbb Z_p\langle X\rangle[X/p]$, $\mathrm{locIdeal} =
> (p) \cdot \mathrm{locSubring}$, and $X = p \cdot (X/p) \in \mathrm{locIdeal}$.
> But $1 + X \notin (\mathrm{locSubring})^\times$ because its formal inverse
> $\sum_{n \geq 0} (-X)^n$ has constant $p$-adic norm $1$ on every coefficient,
> hence is not a restricted power series in $\mathbb Q_p\langle X\rangle$ —
> let alone in the smaller $\mathrm{locSubring}$. Therefore $X \notin
> \operatorname{Jac}(0)$ in $\mathrm{locSubring}$.

The mathematical reason: $\mathrm{locSubring}$ is **not adic-complete**; the
geometric-series argument $(1 - x)^{-1} = \sum x^n$ for $x \in I$ only converges
inside the completion. The relevant Jacobson statement holds only **after**
completing, i.e. at $\mathcal O_X(D)$ — but at that point one no longer has a
useful map back to a less-completed ring to which faithful flatness can transfer
the original problem.

What does still work: faithful flatness of the *product* restriction
$\mathcal O_X(D_0) \to \prod_i \mathcal O_X(D_i)$ from componentwise flatness
(Lemma 8.31, which we have) plus Spa-point spec surjectivity (a Wedhorn 7.45 /
Lemma 8.32 ingredient). This is Theorem 5.9 above — it gives the *cover-level*
Cor 8.32, which is what the proof actually needs. The naive single-map Jacobson
route was a distraction.

**The question is whether to confirm Lane B as parked (only the product-level
Cor 8.32 enters the critical path), or whether there is a salvageable mathematical
reformulation of single-map faithful flatness we should pursue as
secondary infrastructure.**

### 8.4 Single-map restriction injectivity is FALSE

In parallel to Lane B's Jacobson falsity, an earlier architectural assumption was
also disproved. The original sheafiness route relied on:

> *For every rational containment $D \subseteq D_0$, the individual restriction map
> $\mathcal O_X(D_0) \to \mathcal O_X(D)$ is injective (in fact a topological
> embedding).*

This was **disproved** by a counterexample due to Brian Conrad (recorded
2026-04-03):

> **Counterexample 8.4.** Let $A = \mathbb Q_p\langle X\rangle$, $A_0 =
> \mathbb Z_p\langle X\rangle$, $\pi = p$, with the trivial base
> $D_0 = (\emptyset, 1)$ giving $\mathcal O_X(D_0) = A$. Take the rational
> subset $R(\{p, X\}/p)$ — the locus $\{v(p) \neq 0,\ v(X) \leq v(p)\}$.
> Set $D = (P, \{p, X\}, p)$ so $\mathrm{locSubring}_D = A_0[X/p]$. Then
> $X^m \in p^m \cdot A_0[X/p]$ for every $m$, because $X/p \in A_0[X/p]$ gives
> $X^m / p^m \in A_0[X/p]$ hence $X^m \in p^m \cdot A_0[X/p]$. Therefore $X^m$ lies
> in the $m$-th neighbourhood of $0$ in $\mathcal O_X(D)$ for every $m$, so
> $X^m \to 0$ in $\mathcal O_X(D)$ — but $X^m \not\to 0$ in $A = \mathcal O_X(D_0)$
> (its $p$-adic norm stays at $1$). The restriction $A \to \mathcal O_X(D)$ is
> *not* a topological embedding.

The mathematical reason: the localisation topology on $A[1/s]$ is *finer*
on the localised side than the subspace topology inherited from $A$, because
$X/p$ becomes power-bounded after localising and that forces $X$ to be
"topologically smaller" than it is in $A$. So restriction need not be inducing
and need not be injective on completions, even though it is injective on the
underlying algebraic localisation.

What does still work: the **cover-level** product restriction is faithfully
flat and hence injective (Theorem 5.9), and this is what enters the actual
Cor 8.32 / Theorem 8.28(b) proof. The single-map version was never
needed for the theorem; it was a stronger statement we mistakenly tried to use
as a shortcut.

Some downstream wrappers still reference the retired single-map statement
and need to be rerouted to the cover-level form. This is bookkeeping, not
mathematics, but a few hundred lines of refactor.

### 8.5 Architectural questions (subsidiary)

The recent (2026-04-20) refactor moved Lane C from a *τ-based* assembly
(with classical choice mediating the refinement map $\tau$ to the cover)
to a *direct per-$E$* assembly (using a per-$E$ local covering constructed
explicitly from the standard cover's per-$E$ assignment). This decouples
the outer induction from `Classical.choose`-style bookkeeping and matches
Wedhorn's text more closely. We would like a sanity check that this is the
right architectural decision and not introducing subtle structural problems.

---

## 9. Questions for the reviewer

### Q1. Lane B: confirm parking, or salvageable reformulation?

Given Counterexample 8.3, is the right finish:

> Cor 8.32 enters the critical path **only** via its product/cover-level form
> (Theorem 5.9), which is unconditional in our setup modulo the Spa-point spec
> surjectivity. The single-map "Jacobson on locSubring" route is dead and
> stays dead.

— or is there still a mathematically correct reformulation of single-map
faithful flatness that we should pursue as parallel infrastructure
(e.g., a completion-level Jacobson statement combined with a faithful descent
back, or a strengthening assuming $A$ is itself a Jacobson ring)? We are
specifically concerned that future downstream consumers (e.g., proving sheafiness
in the **non-Tate** Huber case) might need single-map injectivity rather than
just product-level injectivity, and would like the reviewer's view on whether
to pre-emptively build infrastructure or trust that the cover-level form
suffices.

### Q2. Lane A: cleanest discharge for the reverse round trip density?

Open lemma 8.1 reduces to "$A\langle X\rangle/(f - X)$ inherits the structure
of a Tate ring in such a way that its Tate algebra has dense polynomials".
Of the three approaches sketched in §8.1, which is the right move:

(a) **Direct.** Construct a pair of definition on $B = A\langle X\rangle/(f-X)$
    explicitly: take the image of $A_0\langle X\rangle$ as the ring of definition,
    image of $\pi A_0\langle X\rangle$ as the ideal of definition. Verify the
    Tate-ring axioms by transfer. (Mostly bookkeeping; some care needed that the
    image is a *subring*, not just additive subgroup.)

(b) **Specialised density lemma.** Bypass the Tate-ring instance and prove a
    one-off statement: "every element of $B\langle Z\rangle$ is a Cauchy limit
    of polynomials in $B[Z]$ in the topology induced from the canonical Tate
    topology on $A\langle X, Z\rangle$". This avoids the pair-of-definition
    construction but introduces a notion of "topology on the quotient ring's
    Tate algebra" that is not the canonical one.

(c) **Abstract universal-property reformulation.** Make the bridge an isomorphism
    of universal Tate rings under $A\langle X\rangle$ killing $(f - X)$, then
    appeal to uniqueness without ever proving density. This requires that the
    Lean universal-property machinery for Tate algebras is rich enough to express
    the appropriate universal characterisation.

We currently lean toward (a) (a few hundred lines of bookkeeping but
mathematically the most honest), but would defer to the reviewer if (c) is
genuinely cleaner.

### Q3. Lane C architecture: τ-based vs direct per-$E$ — is this the right split?

The current Lane C assembly produces a global section by:

1. Picking a standard cover $S$ with per-$E$ assignment $\rho_S : S \to \mathcal C$.
2. For each $E \in \mathcal C$ and each $f \in \rho_S^{-1}(E)$, building the
   Laurent plus/minus pieces $D_0^+(f)$ and $D_0^-(f) \cdot f_0$ at a chosen
   split point $f_0$.
3. Gluing on the per-$E$ local covering (Definition 4.7) using Lane A and Lane B
   applied at $E$.
4. Stitching the per-$E$ outputs into a global section on $D_0$ using
   the compatibility of the original system.

This avoids the older *τ-route*'s appeal to `Classical.choose` on a refinement
map $\tau : \mathcal V \to \mathcal C$. **Is this the right architecture for
formalising Wedhorn Lemma 8.34, or is there a cleaner mathematical packaging
(perhaps closer to Wedhorn's own induction on the cardinality of the standard
cover) we should adopt before locking in the final assembly?**

A specific concern: the "per-$E$" structure adds one extra layer of inner
gluing (the Laurent split happens *inside* $E$ rather than at the level of $D_0$),
which may not match the textbook proof's induction structure where the Laurent
split happens at the level of $D_0$ and refinement propagates outward.

### Q4. Critical-path reality check

Given the current state — Lanes A and C in late assembly, Lane B parked at the
product level, T200-series σ-clearing infrastructure in active development for
the Zavyalov C1 construction — is the route

> **Lane A reverse round trip → Lane C Zavyalov C1 → final assembly via
> direct per-$E$ Part-2**

still the fastest path to a sorry-free `tateAcyclicity` in the strongly noetherian
Tate case? Specifically:

- Is there a reformulation of one of these that would close a substantial chunk
  more cheaply (e.g., proving Open lemma 8.2 directly for noetherian-domain Tate
  rings first, then transferring by quotienting)?
- Is there a different decomposition of the gluing problem we have overlooked that
  would avoid one of the three lanes entirely?
- Or, conversely, is there a *missing* dependency that we have not yet identified
  that will surface once the three current blockers clear — some hidden need for
  a Banach open mapping argument on a non-metrisable space, a Krull intersection
  in a setting where it doesn't apply, or similar?

---

## 10. Auxiliary technical results (appendix)

For completeness, the project has the following relevant infrastructure that the
reviewer does not need to verify but may want to spot-check:

- The Laurent gluing reduction theorem (Theorem 5.10) is rerouted as
  $\mathrm{tateAcyclicity\_gluing\_via\_refinement}$ — it consumes a refinement
  $\mathcal V$ with surjective $\tau$ and outputs the gluing on the original
  $\mathcal C$. Sorry-free.
- The level-1 evaluation map $A\langle X\rangle \to A$ ($X \mapsto 0$) is a
  continuous open surjection in the strongly noetherian Tate case (Wedhorn
  6.18 / module topology on finitely generated $A$-modules). This is used both
  for closedness of the ideal $(1 - sX)$ and for the open mapping step in
  Example 6.38.
- The Banach open mapping theorem in the form
  $\mathrm{AddMonoidHom.isOpenMap\_of\_complete\_countable}$ is available;
  it applies to surjective continuous group homs from countably-generated
  complete spaces onto complete second-countable spaces.
- The Spa-point construction at non-open primes (Wedhorn Lemma 7.45) is proved
  sorry-free in the strongly noetherian Tate case for analytic primes.
  The "non-analytic" / "non-open prime" case is in a separate work stream
  not in the critical path.
- Wedhorn Corollary 7.32 (extraction of a dominating unit from a no-common-zero
  finite family) is proved sorry-free in the form
  "$T \cdot A = A \implies \exists \sigma \in A^\times \, \forall v \in
  \operatorname{Spa}(A, A^+) \, \exists t \in T, v(\sigma) < v(t)$".

---

## 11. Document metadata

- Project name: *Adic spaces* — Lean 4 formalisation following Wedhorn 2019.
- Brief generated: 2026-05-11.
- Length: ~10 pages, ~4,800 words.
- Build status: project compiles; **41** local `sorry`s remain in the principal
  acyclicity file, with the dependency graph above; the algebraic core (row3,
  flatness, generic Stacks 00MA, geometric reduction structure) is sorry-free.
- Recent activity: the T197–T212 commit series (last three weeks) has been building
  Step-2 σ-clearing suppliers (Wedhorn Cor 7.32 transfer into a Lane C C1
  candidate); concurrently the direct per-$E$ Part-2 assembly architecture was
  landed in mid-April.
- Previous reviewer correspondence: the 2026-04-21 overview packet recommended
  the Lane A → Lane C → Lane B-parked finish; this brief asks for confirmation
  given the additional implementation evidence and the explicit
  Counterexample 8.3 to the naive Jacobson route.
