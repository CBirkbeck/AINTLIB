# Paper extraction — "A uniform sheafy Tate domain that is not stably uniform"

Source: `/Users/mcu22seu/Downloads/uniform_sheafy_not_stably_uniform_clarified.pdf` (9 pp., all legible).
Extracted 2026-07-21 for the fjp/cdvf-lemma51 campaign (Phase 0). This file is the campaign's
source of truth for statement faithfulness; the crosswalk in `crosswalk.md` maps it to Lean.

Paper sections: 1 Introduction; 2 Rings of definition and rational localization (eq. (1)–(3),
Def. 2.1); 3 The global ring (eq. (4)–(6), Prop. 3.1, eq. (7)); 4 A nonuniform rational
localization (Prop. 4.1, eq. (8), Cor. 4.2); 5 Localization of the Milnor square (§5.1
Lemma 5.1, eq. (9)–(10); §5.2 Lemma 5.2, eq. (11)–(13); Prop. 5.3, eq. (14)); 6 Sheafiness
(Lemma 6.1, eq. (15); Thm. 6.2; proof of Thm. 1.1). The paper's own terms are *Milnor
square* / *pullback* — it never says "finite-jet"/"FJP" (project-local names).

## 1. Global setup

### 1.1 Base field (verbatim, §1)

"Fix a complete discretely valued nonarchimedean field $k$, with valuation ring $k^\circ$,
uniformizer $\varpi$, and residue field $\tilde{k}$."

That is the entire base hypothesis. No characteristic/perfectness assumptions. $\tilde k$ is
used once (Prop. 3.1: $C_0/\varpi C_0 \cong \tilde{k}[W, W^{-1}, Q]$).

### 1.2 The four integral rings and the pullback (§1, displayed)

$$L_0 = k^\circ\langle W, W^{-1}\rangle, \qquad B_0 = k^\circ\langle W, Q\rangle/(Q^2),$$
$$C_0 = L_0\langle Q\rangle, \qquad D_0 = L_0\langle Q\rangle/(Q^2),$$

where $k^\circ\langle W, W^{-1}\rangle := k^\circ\langle W, V\rangle/(WV - 1)$. Natural maps
$B_0 \to D_0$ (injective; $W \mapsto W$, $Q \mapsto Q$) and $C_0 \twoheadrightarrow D_0$
(quotient). $C_0 \to D_0$ has a continuous $k^\circ$-linear (NOT ring) section by truncation
in $Q$: $f_0 + Qf_1 \mapsto f_0 + Qf_1$.

$$A_0 = B_0 \times_{D_0} C_0, \qquad A = A_0[1/\varpi],$$

topology on $A$ defined by ring of definition $A_0$. Generic fibers: $L = L_0[1/\varpi]$,
$B, C, D$ likewise.

$$(4)\qquad 0 \longrightarrow A_0 \longrightarrow B_0 \oplus C_0 \longrightarrow D_0 \longrightarrow 0$$

is exact (via the section), $A_0$ is $\varpi$-adically complete; after inverting $\varpi$,
a strict Milnor square. "The chosen rings of definition already make the integral row exact,
so no powers of $\varpi$ are lost in the defining square." Since $B_0 \to D_0$ is injective,
$A_0$ embeds in $C_0$:

$$(5)\qquad A_0 = \{ f_0(W) + Qf_1(W) + Q^2 h(W, W^{-1}, Q) : f_0, f_1 \in k^\circ\langle W\rangle,\ h \in C_0 \}.$$

$$(6)\qquad \sum_{(a,b)\in S} c_{a,b} W^a Q^b, \qquad S = \{(a,b) \in \mathbf{Z}\times\mathbf{N} : b \le 1 \Rightarrow a \ge 0\},$$

$c_{a,b} \in k^\circ$, restricted (for every $n$, only finitely many coefficients nonzero
mod $\varpi^n$); $S$ closed under addition. Same with coefficients in $k$ gives $A \subset C$.

**Theorem 1.1 (verbatim).** "The ring $A$ is a complete uniform Tate $k$-algebra and an
integral domain, with $A^\circ = A_0$. The Huber pair $(A, A^\circ)$ is sheafy. However,
$A\langle W/\varpi\rangle \cong k\langle X, Q\rangle/(Q^2)$, $X = W/\varpi$, so $A$ is not
stably uniform."

### 1.3 Rings of definition, lattices, uniformity, strictness (§2)

- $E$ = complete Tate $k$-algebra; ring of definition $E_0$ = open bounded $k^\circ$-subalgebra,
  always chosen $\varpi$-adically complete; then $E = E_0[1/\varpi]$ and $\{\varpi^n E_0\}$ is a
  neighborhood basis of 0.
- Lattice in a complete topological $k$-vector space $M$: open bounded $k^\circ$-submodule $M_0$.
- Power-bounded: $x^n \in \varpi^{-r}E_0\ \forall n$, some $r$. Uniform: $\exists r,\
  \varpi^r E^\circ \subset E_0$. Independent of the ring of definition.
- **Bounded-denominator strictness criterion** (eq. (1), Buzzard–Verberkmoes [1, Lemma 2]):
  continuous $k$-linear $u : M \to N$, lattices $M_0, N_0$; $u$ strict iff $\exists a \ge 0$:

  $$(1)\qquad \varpi^a\big(u(M) \cap N_0\big) \subset u(M_0).$$

  Surjection form: $\varpi^a N_0 \subset u(M_0)$.
- **Definition 2.1 (strict Milnor square, verbatim):** commutative square of complete Tate
  $k$-algebras ($R \to C$, $R \to B$, $C \to D$, $B \to D$) which is cartesian, with
  $0 \to R \to B \oplus C \to D \to 0$ strict exact, and $C \to D$ a strict surjection.

### 1.4 Rational data, Tate algebras, graph ideal (§2)

- Convention: every rational datum has at least one numerator (pad with $f_1 = 0$) — so $m \ge 1$.
- Datum $\alpha = (f_1, \dots, f_m; g)$: ideal $(g, f_1, \dots, f_m)$ open, hence the unit ideal
  ($E$ Tate). After scaling by a power of $\varpi$, all entries in $E_0$.
- $E_\alpha$ = separated $\varpi$-adic completion of $E[1/g]$ for the ring of definition generated
  by $E_0[f_1/g, \dots, f_m/g]$; independent of choices, transitive under refinement. Equivalently:

  $$P_E = E\langle T_1,\dots,T_m\rangle = E_0\langle T_1,\dots,T_m\rangle[1/\varpi], \qquad r_i = gT_i - f_i,$$

  $$(2)\qquad J_{E,\alpha} := (r_1,\dots,r_m) = \mathrm{im}\big(P_E^m \xrightarrow{d_{1,E}} P_E\big), \qquad d_{1,E}(u_1,\dots,u_m) = \sum_i u_i (gT_i - f_i),$$

  the *graph ideal*; before closedness is proved, distinguish $J_{E,\alpha}$ from its closure;

  $$(3)\qquad E_\alpha \cong P_E/\overline{J_{E,\alpha}}.$$

  Refs: Huber [3, (1.2), Prop. 1.3, Lemma 1.5]; Hansen–Kedlaya [2, Def. 3.6].

### 1.5 Local setup for Lemma 5.1 (§5.1, verbatim)

"Let $E$ be one of $B, C, D$, equipped with the displayed ring of definition $E_0$. Let
$f_1, \dots, f_m, g \in E_0$ generate the unit ideal in $E$, put

$$P_E = E\langle T_1,\dots,T_m\rangle, \qquad P_{E,0} = E_0\langle T_1,\dots,T_m\rangle,$$

and set $r_i = gT_i - f_i$."

Notes: unit-ideal condition is in $E$ (not $E_0$); entries in $E_0$; $r_i \in P_{E,0}$.
$A$ deliberately excluded ($A_0$ not noetherian; $B_0, C_0, D_0$ are — "the noetherian vertices").

## 2. Lemma 5.1, verbatim (clause by clause)

Hypotheses: the §5.1 setup above.

1. "The Koszul complex $K_{P_E}(r_1, \dots, r_m)$ is exact in positive degrees."
2. "Every differential is strict, and every image is closed."
3. "In particular, if $d_{1,E} : P_E^m \to P_E$, $J_E = \mathrm{im}(d_{1,E})$, then $J_E$ is closed."
4. "Moreover, there exists $h_E \ge 0$ such that
   $$(9)\qquad \varpi^{h_E}\big(J_E \cap P_{E,0}\big) \subset d_{1,E}\big(P_{E,0}^m\big).$$"
5. "For $E = D$, there also exists $z \ge 0$ such that
   $$(10)\qquad \varpi^{z}\big(\ker(d_{1,D}) \cap P_{D,0}^m\big) \subset d_{2,D}\big(\textstyle\bigwedge^2 P_{D,0}^m\big).$$"

Explicit quantifier structure:
- (9): $\exists h_E \in \mathbb{Z}_{\ge 0}$ (depending on $E$ and the datum) s.t. $\forall x$:
  $x \in J_E$ (ALGEBRAIC image, not closure) $\wedge\ x \in P_{E,0} \Rightarrow \varpi^{h_E} x \in d_{1,E}(P_{E,0}^m)$.
- (10): $\exists z \in \mathbb{Z}_{\ge 0}$ s.t. $\forall s$: $s \in \ker(d_{1,D}) \wedge s \in P_{D,0}^m
  \Rightarrow \varpi^z s \in d_{2,D}(\bigwedge^2 P_{D,0}^m)$. $\bigwedge^2 P_{D,0}^m$ = second
  exterior power of free rank-$m$ over $P_{D,0}$ (rank $\binom m 2$); $d_{2,D}$ preserves
  integrality since $r_i \in P_{D,0}$.
- $z$ has no subscript in the paper; downstream references: "$h_B, h_C, z$ as in lemma 5.1"
  (Lemma 5.2 proof), "$h_D$ as in (9)" (Prop. 5.3 proof).

## 3. The printed proof (four steps)

**Step 1 — polynomial level, primes not containing all $r_i$.** Over $E[T_1,\dots,T_m]$: if
$r_j \notin \mathfrak p$, then $r_j$ is a unit locally; with standard basis $e_1,\dots,e_m$ and
Koszul differential $d$, the degree-1 homotopy $h(\omega) = r_j^{-1} e_j \wedge \omega$ and the
standard identity $d(e_j \wedge \omega) = r_j\,\omega - e_j \wedge d(\omega)$ give
$dh + hd = \mathrm{id}$ — the localized complex is contractible, in particular exact.

**Step 2 — primes containing all $r_i$.** Choose $1 = a_0 g + \sum_i a_i f_i$. Locally
$g(a_0 + \sum_i a_i T_i) = 1 + \sum_i a_i r_i$, a unit, so $g$ is a unit. Translate
$T_i \mapsto T_i + f_i/g$: the sequence $(r_i)$ becomes unit multiples of the coordinate
sequence $(T_i)$, regular over an arbitrary coefficient ring; Koszul of a regular sequence is
exact in positive degrees. (Combining steps 1–2 silently uses: exactness is local at primes.)

**Step 3 — flat base change to $P_E$.** Verbatim: "The rings $E_0$ are noetherian and
$\varpi$-adically complete. The passage from $E[T_1,\dots,T_m]$ to $P_E$ is obtained by
$\varpi$-adic completion and then inverting $\varpi$; it is flat by the flatness of noetherian
completion [4, Tag 00MB]. Exactness therefore passes to $P_E$." I.e.
$E_0[T_\bullet] \to P_{E,0}$ flat (Stacks 00MB), then localize at $\varpi$;
$K_{P_E}(r_\bullet) = K_{E[T_\bullet]}(r_\bullet) \otimes_{E[T_\bullet]} P_E$.

**Step 4 — strictness, closed images, (9)–(10).** Verbatim: "$P_E$ is a complete noetherian
Tate ring. Huber's finite-module results imply that homomorphisms between finite $P_E$-modules
are strict and that their images are closed [3, Lemmas 2.3 and 2.4]. Applying the
bounded-denominator criterion (1) to $d_{1,E}$ and, for $E = D$, to $d_{2,D}$ onto
$\ker(d_{1,D})$, gives (9) and (10)."
- (9) = criterion (1) for strict $d_{1,E}$ with lattices $P_{E,0}^m$, $P_{E,0}$.
- (10) = criterion (1) for strict $d_{2,D}$ viewed onto its image $\ker(d_{1,D})$ (closed, by
  degree-1 exactness + strictness), lattices $\bigwedge^2 P_{D,0}^m$ and $P_{D,0}^m$.
- Constants abstract (mere existence); no effectivity claimed. The concrete $h/z$ bookkeeping
  ($h = \max\{h_B,h_C\}$, total loss $\varpi^{h+z}$, eq. (13)) happens in Lemma 5.2's proof.

## 4. Sign and indexing conventions

- $K_{P_E}(r_1,\dots,r_m)$ indexed HOMOLOGICALLY: $K_p = \bigwedge^p(P_E^m)$, differentials
  LOWER degree, named with degree-first subscripts: $d_{1,E} : P_E^m \to P_E$,
  $d_{2,D} : \bigwedge^2 P_D^m \to P_D^m$. "Exact in positive degrees" = $H_p = 0\ \forall p \ge 1$;
  degree 0 exempt ($H_0 = P_E/J_E$, whose closure-quotient is $E_\alpha$).
- Degree-1 formula (displayed, eq. (2)): $d_{1,E}(u_1,\dots,u_m) = \sum_i u_i r_i$.
- The only displayed signed formula: $d(e_j \wedge \omega) = r_j\,\omega - e_j \wedge d(\omega)$
  (graded Leibniz, $d(e_j) = r_j$, minus on the second factor). Implied general deletion formula
  (not displayed): $d_p(e_{i_1} \wedge \cdots \wedge e_{i_p}) = \sum_{q=1}^{p} (-1)^{q-1}
  r_{i_q}\, e_{i_1} \wedge \cdots \wedge \widehat{e_{i_q}} \wedge \cdots \wedge e_{i_p}$.
- Insertion homotopy wedges $e_j$ on the LEFT: $h(\omega) = r_j^{-1} e_j \wedge \omega$;
  raises degree by 1; $dh + hd = \mathrm{id}$ in every degree.
- These two displayed formulas are the normative data for matching the Lean subset-model sign
  $(-1)^{\#\{j \in J \mid j < i\}}$ (insertion position in ascending order — consistent).
- Handover indexing note: with `koszulDifferential r q : KoszulTerm R m (q+1) →ₗ[R] KoszulTerm R m q`,
  positive-degree exactness is `∀ q : ℕ, Function.Exact (koszulDifferential r (q+1)) (koszulDifferential r q)`
  — exactness at $K_{q+1}$ for all $q \ge 0$, exactly the paper's claim. NOT exactness at $K_0$.

## 5. Dependency graph around Lemma 5.1

Upstream inputs: eq. (1) (strictness criterion, [1, Lemma 2]); eq. (2)–(3) (graph ideal,
[3, (1.2), Prop. 1.3, Lemma 1.5], [2, Def. 3.6]); Stacks Tag 00MB (flatness of noetherian
completion) — the ONLY flatness input; Huber [3, Lemmas 2.3–2.4] (finite modules over complete
noetherian Tate rings: maps strict, images closed) — the ONLY Banach/strictness input.
Silent standard facts: exactness local at primes; coordinate sequence regular over any
coefficient ring; $B_0, C_0, D_0$ noetherian and $\varpi$-adically complete (asserted).

Downstream chain: **5.1 → 5.2 → 5.3 → 6.2 → 1.1**.

- **Lemma 5.2** (main consumer). Setup: datum $\alpha$ in $A$ with entries in $A_0$; for
  $E \in \{A,B,C,D\}$: $P_E, P_{E,0}, d_{1,E}, J_E$.
  $$(11)\qquad 0 \to P_{A,0} \to P_{B,0} \oplus P_{C,0} \to P_{D,0} \to 0$$
  exact (integral row (4) + coefficientwise truncation section); $P_{C,0} \to P_{D,0}$
  surjective, also on finite free modules and their exterior powers.
  Statement: "$J_A$ is closed in $P_A$, and the canonical map $J_A \to J_B \times_{J_D} J_C$
  is an isomorphism. Moreover, $(12)\ 0 \to J_A \to J_B \oplus J_C \to J_D \to 0$ is strict exact."
  Proof uses from 5.1: degree-1 exactness at $D$ (difference of lifts is $d_{2,D}(v_D)$),
  (9) for $B$ and $C$ ($h = \max\{h_B, h_C\}$), (10) for $D$ (correction
  $u'_C = \varpi^z u_C + d_{2,C}(v_C)$, integrality of $d_{2,C}$ only), (11)-descent, yielding
  $$(13)\qquad \varpi^{h+z}\big((J_B \times_{J_D} J_C) \cap (P_{B,0} \oplus P_{C,0})\big) \subset d_{1,A}(P_{A,0}^m),$$
  plus closedness of $J_A$ and strict surjectivity of $J_B \oplus J_C \to J_D$ (uses (9) for $E=D$).
- **Prop. 5.3**: "For every rational datum $\alpha$ in $A$, the canonical sequence
  $(14)\ 0 \to A_\alpha \to B_\alpha \oplus C_\alpha \to D_\alpha \to 0$ is strict exact, and
  $C_\alpha \to D_\alpha$ is a strict surjection. Equivalently
  $A_\alpha \cong B_\alpha \times_{D_\alpha} C_\alpha$. Natural under rational refinement."
  Proof: 5.2 (all four graph ideals closed ⇒ $E_\alpha = P_E/J_E$), rows (11)+(12), rings of
  definition $E_{\alpha,0} = \mathrm{im}(P_{E,0} \to E_\alpha)$, and a second direct use of (9)
  with exponent $h_D$ for left-strictness.
- **Lemma 6.1 (sheaf transfer)**: square of complete Tate Huber pairs; if for every rational
  $U \subset \mathrm{Spa}(R,R^+)$ the section rings form strict exact
  $(15)\ 0 \to \mathcal O_R(U) \to \mathcal O_B(U_B) \oplus \mathcal O_C(U_C) \to \mathcal O_D(U_D) \to 0$
  and $B, C, D$ are sheafy, then $R$ is sheafy as a complete topological ring (sheaf-on-basis
  [4, Tag 009O] + projective-limit topology on arbitrary opens).
- **Thm 6.2**: $(A, A^\circ)$ sheafy — $B, C, D$ affinoid hence sheafy (Huber [3, Thm 2.2]),
  Prop. 5.3 supplies (15), conclude by 6.1.
- Independent of 5.1: Prop. 3.1 ($A$ complete uniform Tate domain, $A^\circ = A_0$; valuation
  $\nu(c) = \max\{n : c \in \varpi^n C_0\}$, eq. (7) $\nu(cc') = \nu(c)+\nu(c')$ via
  $C_0/\varpi C_0 \cong \tilde k[W,W^{-1},Q]$ domain; $A_0 = A \cap C_0$); Prop. 4.1
  ($A\langle W/\varpi\rangle \cong k\langle X,Q\rangle/(Q^2)$ via $G_0 = A_0[W/\varpi]$, eq. (8)
  kills $Q^2 C_0$ in the separated completion); Cor. 4.2 ($k\langle X,Q\rangle/(Q^2)$ not
  uniform: $kQ$ nilpotent, power-bounded, unbounded).

References: [1] Buzzard–Verberkmoes, J. Reine Angew. Math. 740 (2018) 25–39. [2] Hansen–Kedlaya,
Sheafiness criteria for Huber rings, preprint 2025-04-23. [3] Huber, Math. Z. 217 (1994)
513–551. [4] Stacks Project.

## 6. Formalization-facing cautions

1. (9) is about the ALGEBRAIC image $J_E$, not its closure — do not state (9) with $\overline{J_E}$.
2. Constants: $h_E$ for each $E \in \{B,C,D\}$ ($h_D$ used by Prop. 5.3); $z$ for $E = D$ only.
   Datum-dependent; no effectivity.
3. Unit-ideal hypothesis in $E$, entries in $E_0$; $m \ge 1$ by padding.
4. Lemma 5.2 additionally needs: surjectivity of $P_{C,0} \to P_{D,0}$ on free modules AND their
   exterior powers (from the coefficientwise section), exactness of (11); it needs NO strictness
   for $d_{2,C}$, only integrality-preservation.
5. Middle maps of (4), (11), (12), (14) are Milnor difference maps; formula never displayed.
