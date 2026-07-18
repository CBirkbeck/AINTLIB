# Review brief (topic-scoped: T-W7) — Constructive group-scheme structure on a Weierstrass elliptic curve over a base

*Prepared 2026-07-07 for a senior arithmetic geometer (expert in abelian schemes and the moduli of
elliptic curves). Self-contained: no repository access required. **This is a topic-scoped brief** —
it concerns only the construction of the group law on an elliptic curve over a base and its
uniqueness; the separate whole-programme brief covers the rest of the project. The formalisation is in
the Lean theorem prover, but every question below is purely mathematical; formalisation constraints
are stated in words where they matter.*

---

## 1. Goal

Let $S$ be an arbitrary scheme (in particular possibly non-reduced) and let $\pi : E \to S$ be a
morphism that is **smooth, proper, of relative dimension one**, equipped with a section
$e : S \to E$, and that is **locally Weierstrass** in the sense of §2.1 below. We want, entirely
constructively:

1. **(Existence)** a structure of **commutative group scheme over $S$** on $\pi : E \to S$ with
   identity section $e$ — morphisms $m : E \times_S E \to E$ (multiplication) and $\iota : E \to E$
   (inverse) over $S$, satisfying associativity, commutativity, the unit axioms with respect to $e$,
   and the inverse axioms, all as **identities of $S$-morphisms**.
2. **(Canonicity)** that this group structure is the **unique** one with identity $e$: any two
   group-scheme structures on $E/S$ sharing the identity section $e$ coincide.

The context is a formal development of the moduli stack of elliptic curves, where "an elliptic curve
over $S$" must carry its group law as constructed data, canonically attached to $(\pi, e)$.

We seek **strategic and soundness guidance on three genuinely hard steps** — the group-law *morphism*
construction, the sheaf-pushforward identity $\pi_*\mathcal O_E = \mathcal O_S$, and the rigidity lemma
over an arbitrary base — plus a **sanity check on the overall reduction strategy**.

---

## 2. Background, setting, and references

### 2.1. The setting

**Weierstrass curves.** For a commutative ring $R$, a *Weierstrass curve* is coefficients
$a_1,\dots,a_6 \in R$; it has a discriminant $\Delta \in R$, and is *elliptic* when $\Delta \in
R^\times$. Its *projective Weierstrass model* $W \subset \mathbb P^2_R$ is $Y^2Z + a_1XYZ + a_3YZ^2 =
X^3 + a_2X^2Z + a_4XZ^2 + a_6Z^3$, a proper smooth curve over $\operatorname{Spec} R$ (when elliptic)
with distinguished point at infinity $O = [0:1:0]$, taken as the section $e$.

**The affine chord–tangent group law (over a field).** Over a field $k$, the $k$-points of the affine
Weierstrass curve together with $O$ form an abelian group under the classical chord–tangent
construction, given by explicit rational formulas: for $P_1=(x_1,y_1)$, $P_2=(x_2,y_2)$ with
$x_1\neq x_2$, the secant slope is $\lambda=(y_1-y_2)/(x_1-x_2)$ and
$x_3=\lambda^2+a_1\lambda-a_2-x_1-x_2$, with $y_3$ the corresponding value; the doubling case uses the
tangent slope; and $P+(-P)=O$. In the formal development this field-level abelian group is already
available as a black box (standard, fully formalised in the library we build on).

**Local Weierstrass structure.** $\pi : E \to S$ is *locally Weierstrass* if, Zariski-locally on $S$ —
over an affine open $\operatorname{Spec}\Gamma_i \subseteq S$ — there is a Weierstrass curve $W_i$ over
$\Gamma_i$ with invertible discriminant and an isomorphism of $\Gamma_i$-schemes between the
restriction of $E$ and the projective Weierstrass model of $W_i$ **carrying $e$ to the point at
infinity**.

**The universal Weierstrass curve.** Let $R_{\mathrm{univ}} = \mathbb Z[a_1,\dots,a_6][\Delta^{-1}]$,
the polynomial ring in the five coefficients with the discriminant inverted — an **integral domain**.
Let $U = \operatorname{Spec}R_{\mathrm{univ}}$ and $E_U \to U$ the projective Weierstrass model of the
tautological Weierstrass curve ($a_i$ the coordinate functions). Then $E_U/U$ is elliptic, and every
elliptic Weierstrass curve over every ring is a base change of $E_U$ along the classifying map
$R_{\mathrm{univ}}\to\Gamma$, $a_i\mapsto$(its coefficients) — well-defined precisely because $\Delta$
maps to a unit. Write $K=\operatorname{Frac}R_{\mathrm{univ}}$ and $E_{U,K}$ for the generic fibre.

**Variable changes.** The group $\mathrm{VC}$ of Weierstrass variable changes (the $(u,r,s,t)$ acting
on coefficients and coordinates) acts; two local Weierstrass presentations on an overlap differ by such
a variable change. It is **established** that the affine addition formulas ($x_3$, $y_3$, the slope,
negation) are **invariant under variable changes** at the coordinate level, giving a cocycle
compatibility used for gluing.

### 2.2. References

- **[GIT]** Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, 3rd ed., Springer 1994. Prop. 6.1 is
  the **rigidity lemma**. *(Canonical source for Q3; we currently lack access to its proof and want the
  reviewer's help reconstructing it formalisation-friendly.)*
- **[FC]** Faltings–Chai, *Degeneration of Abelian Varieties*, Ergebnisse 22, Springer 1990. Ch. I §1:
  an abelian scheme is a smooth proper group scheme with geometrically connected fibres; Rem. 1.2(b)
  deduces commutativity from [GIT] 6.1 (**cited, not proved**); 1.2(c): "geometrically connected" may be
  relaxed to "connected"; Thm 1.2.7 extends homomorphisms over a **normal** base.
- **[KM]** Katz–Mazur, *Arithmetic Moduli of Elliptic Curves*, Ann. Math. Studies 108, Princeton 1985.
- **[Sil]** Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106, Springer 2009. Ch. III;
  III.3.6: the group law is a morphism (over a field).
- **[Del]** Deligne, *Courbes elliptiques: formulaire (d'après J. Tate)*, LNM 476, 1975.

### 2.3. State of the art

Classical: Weierstrass/Tate (formulas), Mumford (rigidity), Katz–Mazur (moduli). Nothing here is new;
the difficulty is a **constructive, base-independent** account with **explicit reductions**, because
(a) the target base $S$ may be non-reduced, so pointwise/density arguments on $S$ are unavailable, and
(b) the proof assistant's library currently lacks relative coherent-cohomology-and-base-change and the
rigidity lemma, so any step needing those must be reduced to something elementary or built from
scratch — and we want to know *which* before investing.

---

## 3. Strategy

Organising principle: **construct the group law once, over the universal integral atlas $U$, and obtain
it on every $E/S$ by base change and gluing.**

1. **Construct $m_U : E_U \times_U E_U \to E_U$ and $\iota_U : E_U \to E_U$** as honest morphisms over
   the *domain* $R_{\mathrm{univ}}$ (negation is denominator-free and easy; multiplication is **Q1**).
2. **Prove the group axioms for $m_U$ over $U$** — associativity, commutativity, unit, inverse — as
   morphism identities, each by: restricting to the **generic fibre** $E_{U,K}$, where $m_U$ agrees
   with the field chord–tangent group law over $K$ (**Q4a**), an abelian group (the field black box);
   using that $E_U^{\times n}$ is **integral** (**Q4b**), so the generic point is dense and
   $E_U^{\times n}$ reduced; and concluding by the available fact **two morphisms from a reduced scheme
   to a separated scheme agreeing on a dense (dominant) subscheme are equal**. So the axioms hold over
   $U$ with **no rigidity and no cohomology**.
3. **Descend to general $E/S$.** Each local Weierstrass chart is a base change of $E_U$ along its
   classifying map; define $m$ on each chart as the base change of $m_U$, and **glue** (charts agree on
   overlaps by the variable-change invariance cocycle of §2.1). Every group axiom on $E/S$ holds
   chart-locally **by base change** of the universal identity — a base-change/gluing argument, **not** a
   density argument on $S$, hence valid even when $S$ is non-reduced. This gives **Existence**.
4. **Canonicity** is separate. Two group structures $m,m'$ with the same identity $e$: show the
   identity map is a homomorphism $(E,m)\to(E,m')$, so $m=m'$. Standard tool: the **rigidity lemma**
   ([GIT] 6.1) — a pointed $S$-morphism of abelian schemes is a homomorphism — whose hypothesis is
   $\pi_*\mathcal O_E=\mathcal O_S$ universally (**Q2**); the lemma itself is **Q3**.

---

## 4. Established results

- **The universal elliptic curve $E_U\to U$**: smooth, proper, relative dimension one, with zero
  section, a global Weierstrass model over $U$. (Complete, machine-checked.)
- **Variable-change invariance of the affine group law** (the gluing cocycle): addition, negation, slope
  invariant under variable changes, with naturality and cocycle compatibilities. (Complete — ~40
  interlocking lemmas.)
- **Verified library infrastructure**: (i) "reduced source + separated target + dominant image ⇒ two
  morphisms agreeing there are equal"; (ii) gluing morphisms along an open cover from overlap
  compatibility, with uniqueness; (iii) rational/partial maps with dense domain; (iv) the affine
  chord–tangent formulas with on-curve and non-singularity lemmas; (v) the field abelian group law.
- **Verified library gap**: no relative coherent-cohomology-and-base-change, no Stein factorisation, no
  rigidity lemma. Steps 2–3 avoid all of these; step 4 (canonicity) cannot.

---

## 5. Where we are stuck / the hard steps

### 5.1. Constructing the multiplication *morphism* $m_U$ (Q1)

The field group law is a **case split** on equality of points ($x_1=x_2$? $P_2=-P_1$? $P_i=O$?), using
decidability of equality in a field. This does **not** globalise to a scheme morphism — one cannot
decide $x_1=x_2$ scheme-theoretically. So $m_U$ must be built on an open cover where each piece is
given by formulas *regular there*, glued; or by a total construction. The secant formula is regular
only on $\{x_1\neq x_2\}$; the diagonal (doubling), the anti-diagonal $\{P_2=-P_1\}$ (sum $=O$), and
loci through $O$ each need separate handling, and the pieces must (a) cover, (b) agree on overlaps, (c)
land on the curve. This is the **single most delicate construction** in the project.

### 5.2. The pushforward identity $\pi_*\mathcal O_E=\mathcal O_S$ (Q2)

Rigidity needs $\mathcal O_S\xrightarrow{\sim}\pi_*\mathcal O_E$, stably under base change (proper,
geometrically connected reduced fibres, $H^0=$ base field). For genus one: global functions on a fibre
are constant. In general this is cohomology-and-base-change (Grauert), which the library lacks. Is there
an **elementary** route for a Weierstrass model?

### 5.3. The rigidity lemma over an arbitrary base (Q3)

We need [GIT] 6.1: if $p:X\to S$ is proper flat with $\pi_*\mathcal O_X=\mathcal O_S$ universally, and
$f:X\times_S Y\to Z$ is an $S$-morphism constant along $X_{s_0}\times\{y_0\}$, then $f$ factors through
the projection to $Y$ near $y_0$; and the corollary that a **pointed morphism of abelian schemes is a
homomorphism**. We lack the source's proof and will not reconstruct it from memory.

### 5.4. Generic-fibre bridge and integrality (Q4)

Step 2 needs: (a) the precise sense in which $m_U|_{E_{U,K}}$ **is** the field chord–tangent addition
over $K$ — bridging a scheme morphism and the library's field-point group operation; (b) that
$E_U^{\times n}$ is integral, with clean hypotheses (smoothness over a domain; geometric integrality of
elliptic-curve fibres; integrality under fibre products over an irreducible base).

---

## 6. Open mathematical questions for the reviewer

> **Q1 (the multiplication morphism).** Cleanest construction of $m_U:E_U\times_U E_U\to E_U$ over the
> *domain* $R_{\mathrm{univ}}$ for a formal, base-independent development? (i) Is the "third
> intersection point of the line through $P,Q$ with the cubic" a **total** morphism given by
> resultant/projective formulas (so $P+Q=-(P*Q)$ needs no case split), and preferable to
> affine-cover-and-glue? (ii) In the cover approach, a clean finite cover of $E_U\times_U E_U$ handling
> the diagonal, the anti-diagonal $\{P_2=-P_1\}$, and the loci through $O$ — and the best treatment of
> $O$ (projective chart vs. translation)? (iii) Does the secant rational map extend across
> $\{x_1=x_2\}$ to a morphism by a clean argument (target proper, source smooth of relative dimension
> two), or must the extension be exhibited by explicit formulas?

> **Q2 ($\pi_*\mathcal O=\mathcal O$).** For an elliptic curve as a projective Weierstrass model over a
> base, is there an **elementary** proof that $\pi_*\mathcal O_E=\mathcal O_S$ universally — a direct
> $H^0$ computation on the explicit model, or via the section $e$ and ampleness of $O$ — avoiding
> general cohomology-and-base-change? May one prove it for $E_U/U$ (integral base) and obtain it for all
> $S$ by base change, and what flatness/constancy input does that base change need?

> **Q3 (rigidity).** A **formalisation-friendly statement and proof** of [GIT] 6.1 over an arbitrary
> base, and of "a pointed morphism of abelian schemes is a homomorphism". (a) In the classical proof
> (take affine $V\ni z_0$; the proper projection of $f^{-1}(Z\setminus V)$ is closed and misses $y_0$;
> a morphism to an affine constant on proper connected reduced fibres factors through the base) — which
> ingredient is the real formalisation obstruction, and is "constant on fibres ⇒ factors" best done via
> $\pi_*\mathcal O=\mathcal O$ directly? (b) For **our** application, may the base be assumed **reduced
> or normal** without loss — is canonicity over non-reduced $S$ needed for the moduli application, or
> does it follow from the reduced case plus the moduli stack's universal property? If the latter, we
> avoid the arbitrary-base rigidity lemma entirely.

> **Q4 (generic-fibre bridge; integrality).** (a) Cleanest way to state and prove $m_U|_{E_{U,K}}$
> equals the field chord–tangent addition — bridging a morphism of $K$-schemes and the abstract group
> operation on $K$-points? Does checking agreement on $\{x_1\neq x_2\}$ (both the secant formula) plus
> density suffice, given $E_{U,K}\times_K E_{U,K}$ integral? (b) Minimal clean hypotheses for
> $E_U^{\times n}$ integral (reduced $+$ irreducible)?

> **Q5 (soundness of the reduction).** Is §3 sound — legitimate to prove the group axioms as **morphism
> identities over the universal integral atlas** and obtain them over an **arbitrary (possibly
> non-reduced) $S$** purely by base change and gluing along local Weierstrass charts, with **no** appeal
> to reducedness of $S$? Pitfalls to anticipate (classifying map non-flat; chart multiplications failing
> to glue)?

> **Q6 (alternative to rigidity for canonicity).** Independently of Q3: a construction-level proof of
> **uniqueness** of the group law with given identity avoiding rigidity — e.g. characterising $m$ as the
> unique morphism restricting to the chord–tangent map on a dense open, using $E\times_S E$ flat over
> $S$ and the graph closed? Would it survive over a non-reduced base?

---

## 7. Document metadata

- Project: constructive group-scheme structure on a locally-Weierstrass elliptic curve over a base
  (part of a formalisation of the moduli stack of elliptic curves). **Topic-scoped brief** — see the
  separate whole-programme brief for the rest.
- Brief generated: 2026-07-07.
- Build status: the universal curve and the variable-change-invariance cocycle are complete and
  machine-checked; the group law itself (this brief's subject) is not yet started, pending the
  strategic decisions above.
- Board tickets targeted: `mulHom_universal` (Q1), `properPushforwardStructureSheaf` (Q2),
  `rigidityLemma` (Q3), atlas axioms via the generic fibre (Q4/Q5), `abelEnrichment_unique` (Q3/Q6).
