# Review brief — Arithmetic moduli of elliptic curves and modular curves, formalisation programme

*Prepared 2026-07-05 for a senior arithmetic geometer. Self-contained: no repository
access required. **DRAFT** — question list pending final sign-off by the project owner.*

## 1. Goal

We are beginning a machine-verified (Lean 4 / mathlib) development of the theory of
modular curves **as moduli spaces of elliptic curves**, in the style of Katz–Mazur. The
programme, in increasing order of ambition:

1. **Elliptic curves over an arbitrary base scheme** — the definition, the group law,
   the multiplication maps $[N]$, and the torsion subgroup schemes $E[N]$.
2. **The Weil pairing** $e_N\colon E[N]\times_S E[N]\to \mu_N$ over an arbitrary base.
3. **Drinfeld level structures** (relative effective Cartier divisors, "full sets of
   sections", points of exact order $N$), taken as the *definitions of record* over any
   base, with the naive fibrewise notions recovered as theorems when $N$ is invertible.
4. **The Katz–Mazur moduli formalism**: the category $\mathrm{Ell}/R$, moduli problems
   as contravariant set-valued functors on it, relative representability, rigidity, and
   the theorem *representable $\iff$ relatively representable and rigid*; alongside it,
   honest stack-theoretic statements (fppf descent of elliptic curves) — Katz–Mazur
   famously use stacks without saying so, and we surface that content explicitly.
5. **Representability where it holds**: the Tate normal form and the universal curve
   with a point of order $>3$ over $\mathbb{Z}[A,B][\Delta^{-1}]$; $Y_1(N)$ for
   $N\ge 4$ and $Y(N)$ for $N\ge 3$, smooth and affine over $\mathbb{Z}[1/N]$.
6. **The twisted modular curve $Y(\bar\rho)$** over $\mathbb{Q}$: given a continuous
   $\bar\rho\colon\mathrm{Gal}(\bar{\mathbb{Q}}/\mathbb{Q})\to
   \mathrm{GL}_2(\mathbb{Z}/N)$ with cyclotomic determinant and a choice $p$ of
   Galois-equivariant identification $\Lambda^2\bar\rho\cong\mu_N$, the smooth affine
   geometrically irreducible curve over $\mathbb{Q}$ representing "elliptic curves $E$
   with $E[N]\cong\bar\rho$ as representations-with-pairing". This is the input needed
   for the Moret–Bailly/prime-switching arguments in the ongoing formalisation of
   Fermat's Last Theorem; the downstream applications treat it as a black box, but the
   curve itself must be built honestly.

The immediate deliverable under review is not proofs but a **plan**: a complete
scaffold of definitions and theorem statements (every statement type-checks against
the current mathlib; proofs deferred), a decomposition of the work into tickets for
parallel execution, and the design decisions below. We ask the reviewer to audit the
*definitions and the decomposition*, because these will be extremely expensive to
change later: the definition of an elliptic curve over a scheme and of the Weil pairing
will be consumed by every later arithmetic development (Mazur-style torsion theorems,
modularity), so "make a definition, use it, regret it" is the failure mode we are
guarding against.

## 2. Background and references

### 2.1 Setting and conventions

All schemes are arbitrary (no noetherian hypotheses unless stated). For a scheme $S$
and $N\ge 1$, "$N$ invertible on $S$" means $N$ is a unit in $\Gamma(S,\mathcal{O}_S)$.
"Geometric point" means a morphism from the spectrum of an algebraically closed field.
$\mu_N$ denotes the group scheme of $N$-th roots of unity,
$\mu_N=\operatorname{Spec}\mathbb{Z}[T]/(T^N-1)$, base-changed as needed. For a
Weierstrass equation $W$ over a commutative ring $R$ (coefficients
$a_1,a_2,a_3,a_4,a_6$), $\Delta(W)$ is its discriminant; "elliptic Weierstrass curve"
means $\Delta(W)\in R^\times$. The division polynomials are denoted $\psi_n$.

### 2.2 References

- [KM] N. Katz, B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Math.
  Studies 108, Princeton, 1985. (Primary. Currently available to the project: the
  Introduction and Ch. 1 §§1.1–1.9 in full; the remainder is on order — several
  decomposition leaves are explicitly gated on quote-checking against the full text.)
- [Loe] D. Loeffler, *Modular Curves*, lecture notes (21 pp.), §§3.3–3.8. (Complete;
  the concise spine for the first two phases.)
- [Buz] K. Buzzard, *Formalizing Fermat*, Lecture 8 slides (26 March 2026), pp. 33–40.
  (The specification of $Y(\bar\rho)$ and its application.)
- [Hida] H. Hida, *Geometric Modular Forms and Elliptic Curves*, World Scientific,
  2001. (Full text in hand; secondary source for the [KM] Ch. 2 material.)
- [Katz] N. Katz, *p-adic properties of modular schemes and modular forms*, Antwerp
  III, LNM 350, 1973. (Full text; later phases.)
- [Sil] J. Silverman, *The Arithmetic of Elliptic Curves*, GTM 106. (Used strictly
  fibrewise, over fields.)
- SGA 1 VIII (fppf descent), EGA IV 11.3.10 (flatness by fibres), Oort–Tate/Deligne
  (finite locally free commutative group schemes of rank $N$ are killed by $N$) — as
  named black boxes, see §6.

### 2.3 State of the art in the proof assistant

The ambient library (mathlib) has: Weierstrass equations over arbitrary commutative
rings with discriminants, $j$-invariants, isomorphism-of-models theory and division
polynomials; the group law on points **over fields only**; a mature theory of scheme
morphisms (smooth, étale, proper, finite, flat, with fibres, Zariski's main theorem,
valuative criteria); group objects in the category of schemes over a base; the
fppf/fpqc pretopologies and an abstract theory of fibered categories and stacks; the
cyclotomic character; and the absolute Galois group with its Krull topology. It has
**none** of: elliptic curves over a base scheme, the Weil pairing (over any base,
including fields), torsion subgroup *schemes*, level structures, moduli problems,
$\mu_N$ as a group scheme, Cartier duality, effective Cartier divisors, coherent
cohomology (hence no genus, no Riemann–Roch), Picard functors, quotients of schemes by
finite group actions, or algebraic spaces/stacks. Separately, a sibling project in the
same repository has, **over fields**: the Weil pairing on $\ell$-torsion of elliptic
curves with bilinearity/nondegeneracy (algebraically closed case), the structure
theorem $E[N](\bar k)\cong(\mathbb{Z}/N)^2$ for $N$ invertible, Tate modules, and dual
isogenies — we intend to reuse these as the fibrewise anchors, never re-proving them.

## 3. Strategy

Six parallel workstreams: (A) elliptic curves over a base; (B) torsion and the basic
finite group schemes; (C) the Weil pairing; (D) Drinfeld level structures ([KM] Ch. 1,
which we possess in full); (E) the moduli formalism and the representability results,
beginning with a fully elementary, provable-immediately layer (Tate normal form,
after [Loe] §3.3); (F) the twisted curve $Y(\bar\rho)$. Definitions are stated in
Katz–Mazur generality from the start; the *theorem* programme is staged: first over
bases where $N$ is invertible (everything needed for $Y(\bar\rho)$ and characteristic-0
applications), with the characteristic-$p\mid N$ theory ([KM] Ch. 5–7: regularity,
cyclicity, quotients) as explicitly planned later phases. Statements are never weakened
to fit the staging.

Two disciplines shape the whole plan and deserve the reviewer's scrutiny:

**(i) The registered-data discipline.** Some objects are *canonical data*, not
properties — the group law on $E/S$, the Weil pairing, the sum of Cartier divisors, the
finite étale $\mathbb{Q}$-group scheme attached to $\bar\rho$. Each such object enters
the development once, as a named registered construction with (a) its precise
mathematical definition recorded, (b) a dedicated construction task, and (c)
*specification theorems* that pin it down uniquely (e.g. the group law is the unique
group structure with the zero section as identity; the pairing is pinned by its
fibrewise comparison with the classical pairing). All downstream mathematics is
required to consume these objects **only through the stated specifications**, so that
nothing can silently depend on an unstated property of an unconstructed object.

**(ii) The black-box register.** Standard hard inputs are stated as named, isolated
assumptions to be discharged later or accepted as permanent imports: Riemann–Roch
consequences over a field (a pointed smooth proper geometrically connected genus-1
curve is a plane Weierstrass cubic); cohomology-and-base-change (for the Abel
isomorphism); the fibrewise flatness criterion; the Oort–Tate/Deligne "killed by rank";
fppf descent of schemes; and the complex-analytic geometric irreducibility of modular
curves ("see 1980s").

## 4. The definitions (the heart of the review)

**Definition 4.1 (elliptic curve over a scheme).** An *elliptic curve over $S$* is a
morphism $\pi\colon E\to S$, smooth of relative dimension 1 and proper, together with a
section $0\colon S\to E$, such that every fibre, pointed by the section, is a genus-1
curve in the following operational sense: for each $s\in S$ there is an elliptic
Weierstrass curve $W$ over the residue field $\kappa(s)$ such that the fibre $E_s$,
with its point $0(s)$, is a Weierstrass model of $W$ — meaning a proper, finitely
presented pointed $\kappa(s)$-scheme whose points over every field extension
$K/\kappa(s)$ are naturally identified with the Weierstrass points of $W_K$ (including
the point at infinity, which corresponds to the base point).

*Why this shape.* All sources define the fibre condition as "smooth proper
geometrically connected of genus 1". Genus is a cohomological notion, and the ambient
library has no coherent cohomology; waiting for it would delay the definition by
months. Over a field, Riemann–Roch makes the two conditions equivalent (the black box
BB-RR), and the equivalence is recorded as a theorem obligation to be stated the moment
a genus exists. The projective Weierstrass model itself (the plane cubic as a scheme,
with its section at infinity) is one of the registered constructions, built by gluing
the two standard affine charts.

**Definition 4.2 (the group law — a theorem, not a datum of 4.1).** The group
structure on $E/S$ is *not* part of Definition 4.1. It is registered as canonical data:
a commutative group structure on $E$ in the category of $S$-schemes with identity the
zero section, unique with that property, constructed via Abel's theorem
$E(T)\cong\operatorname{Pic}^0(E_T/T)$ ([KM] 2.1.2). Uniqueness and commutativity are
stated as the pinning specifications. $[N]$ is the $N$-th power of the identity in the
endomorphism monoid this induces, and $E[N]$ is the scheme-theoretic kernel
$E\times_{[N],E,0}S$.

**Definition 4.3 (relative effective Cartier divisors — working form).** In a smooth
relative curve $C/S$, we take as working definition: a closed subscheme $D\subseteq C$
which is finite locally free over $S$; its degree is the rank. The official definition
(closed subscheme, flat over $S$, with invertible ideal sheaf) is recorded, and the
equivalence in the smooth-curve case is an explicit obligation gated on a line-bundle
API. The divisor $\sum_i[P_i]$ attached to finitely many sections is registered data
(ideal products), with degree and base-change specifications.

**Definition 4.4 (Drinfeld structures — [KM] 1.3.6, 1.4.1, verbatim transcriptions).**
A divisor $D$ in $E/S$ *is a subgroup* if for every $T\to S$ the subset
$D(T)\subseteq E(T)$ is a subgroup. A point $P\in E(S)$ has *exact order $N$* if
$[P]+[2P]+\cdots+[NP]$ is a subgroup of $E/S$. A $\Gamma_1(N)$-structure is a point of
exact order $N$; a $\Gamma(N)$-structure is a pair $P,Q$, killed by $N$, with
$\sum_{a,b}[aP+bQ]=E[N]$ as divisors; a $\Gamma_0(N)$-structure is a rank-$N$ cyclic
subgroup divisor. Katz–Mazur's Caution 1.4.3 (over $\mathbb{F}_p$ the zero section has
exact order $p^n$ for every $n$) is kept prominently: "order" is not a function of $P$.
When $N$ is invertible, [KM] 1.4.4 recovers the naive fibrewise notions — these
equivalences are theorem obligations with the full [KM] proofs already in hand.

**Definition 4.5 (moduli problems — [KM] Ch. 4 / [Loe] §3.7, verbatim).** The category
$\mathrm{Ell}/R$ has objects the pairs ($R$-scheme $S$, elliptic curve $E/S$) and
morphisms the cartesian squares. A moduli problem is a contravariant set-valued functor
on it; *relatively representable* and *rigid* are as in [KM]; the theorem
*representable $\iff$ relatively representable and rigid* is stated (its hard direction
consumes quotients of quasi-projective schemes by finite groups — an explicit API gap —
via the naive-level-3/Legendre bootstrap and gluing over $\mathbb{Z}[1/6]$). The
stack-theoretic content is carried by two concrete statements: elliptic curves descend
along fppf covers (effectivity), and relatively representable problems are fppf-local;
the packaging of $S\mapsto\{\text{elliptic curves}/S\}$ as a fibered category/stack
object is a deliberately deferred, non-load-bearing bridge task.

**Definition 4.6 (the datum for $Y(\bar\rho)$ — after [Buz] p. 33).** A level datum is
a continuous $\bar\rho\colon G_{\mathbb{Q}}\to\mathrm{GL}_2(\mathbb{Z}/N)$ (open
kernel) with $\det\bar\rho$ the mod-$N$ cyclotomic character, together with a
Galois-equivariant isomorphism $p$ from $\mathbb{Z}/N$ (with the $\det\bar\rho$-action)
to $\mu_N(\bar{\mathbb{Q}})$. To $\bar\rho$ is attached (registered construction,
Grothendieck–Galois) a finite étale $\mathbb{Q}$-group scheme $V_{\bar\rho}$ of order
$N^2$ whose $\bar{\mathbb{Q}}$-points realise $\bar\rho$. A *$\bar\rho$-level
structure* on $E/T$ ($T$ a $\mathbb{Q}$-scheme) is an isomorphism
$E[N]\cong V_{\bar\rho}\times_{\mathbb{Q}}T$ of group schemes over $T$ carrying the
Weil pairing to $p$ (equivalently: to the standard symplectic pairing on
$(\mathbb{Z}/N)^2$ transported by $p$). The main statement: for $N\ge 3$ this moduli
problem is representable by a smooth affine curve $Y(\bar\rho)/\mathbb{Q}$,
geometrically irreducible (black box), whose points over any $\mathbb{Q}$-scheme are
naturally the isomorphism classes of pairs $(E,\alpha)$. The planned construction is
Galois-descent twisting of $Y(N)_{\mathbb{Q}}$ by the cocycle of $\bar\rho$.

## 5. What exists already (established or transcription-complete)

- The full statement scaffold for §§4.1–4.6 type-checks (73 deferred proofs; the
  registered-data and black-box registers are as in §3).
- Transcription-faithful sources with proofs in hand for: all of [KM] Ch. 1 §§1.1–1.9
  (Cartier divisors, full sets of sections via the universal norm equation, exact
  order, the 1.4.4 equivalences); all of [Loe] (Tate normal form with proof; explicit
  $Y_1(5)$ and $Y_1(N)$; smoothness of $Y_1(N)$; quotients and $Y_0(N)$ as a coarse
  object with the explicit failure of fine representability; the $\mathrm{Ell}/R$
  formalism and the representability criterion; the $\mathcal{P}_H$ machinery,
  including the relative representability of full level via non-vanishing of Weil
  pairings, and the rigidity criterion "no elliptic elements and $-1\notin H$").
- Two results are marked "provable immediately" and are the first execution targets:
  the ring-level Tate normal form ([Loe] 3.3.4: unique change of variables to
  $Y^2+\alpha XY+\beta Y=X^3+\beta X^2$ carrying a nowhere-order-$\le 3$ point to
  $(0,0)$, the order condition expressed as $\psi_2\psi_3$ being a unit), and the
  universal property of $\mathbb{Z}[A,B][\Delta^{-1}]$.

## 6. Ticket board (compact view; mathematically-named)

| Ticket | Content | Depends on | Status |
|---|---|---|---|
| tate-normal-form | [Loe] 3.3.4, ring level | — | ready (provable now) |
| universal-tate-curve | [Loe] 3.3.5, ring level | — | ready (provable now) |
| weierstrass-proj-model | plane cubic as glued scheme + interface | — | ready |
| model-smooth-iff-Δ-unit / model-uniqueness | smoothness; uniqueness (RR box) | model | ready / KM-gated |
| base-change-elliptic | stability of the definition | — | ready |
| abel-group-law | Pic⁰, Abel, uniqueness, commutativity | model, divisors | hardest chain; route Q3 |
| mu-N-wiring | μ_N, (ℤ/N), points | — | ready |
| torsion-closed-immersion / torsion-rank-N² / [N]-étale | E[N] basics; KM 2.3.1; [Loe] 3.4.2 | group law | statements final |
| torsion-fibre-comparison | reuse of the field-level (ℤ/N)² theorem | — | ready |
| weil-pairing-construction | KM 2.8 (route Q5) | torsion, μ_N, divisors | KM-gated |
| pairing-specs + field-comparison | bilinear/alternating/nondegenerate; normalisation pin (Q6) | construction | ready after it |
| divisor-sums | Σ[Pᵢ] with degree/base-change | — | ready |
| full-sections-reduced-criterion | [KM] 1.9.2 | — | ready (proof in hand) |
| exact-order-killed / 1.4.4-geometric / 1.4.4-étale | [KM] 1.4.2/1.4.4 | divisor-sums | ready (proofs in hand) |
| Γ(N)-drinfeld-vs-naive, Γ₁ version, Γ₀-fppf | [KM] Ch. 3 + 1.4.4 | above | partially KM-gated |
| ell-category-plumbing / functor-laws | 𝑬𝒍𝒍/R mechanics | — | ready |
| KM-4.7 | representability criterion | finite-quotients gap | gated on AG-QUOT |
| Y₁(N) | representable, smooth affine, N ≥ 4 | tate tickets + 1.4.4 + [N]-étale | milestone |
| Y(N) | rigid + representable, N ≥ 3 | KM-4.7 or explicit route; Weil pairing | milestone |
| fppf-descent-of-elliptic-curves / fppf-separatedness / stack-packaging | the stack bridge | base-change | ready / deferred |
| V-ρ-construction | Grothendieck–Galois (gap AG-GG) | — | scoping |
| Y(ρ̄) | twist of Y(N); points description | Y(N), V_ρ, pairing pin | phase-3 milestone |
| geometric-irreducibility | black box (1980s) | Y(ρ̄) | permanent box (acceptable) |

## 7. Where we are stuck / the decision points

**7.1 The definition bottleneck (genus).** Every faithful route to "genus-1 fibres"
needs one genuine geometric object first: coherent cohomology (months), or the plane
projective model (weeks). We chose the model. The risk we want assessed: consumers of
the definition (e.g. a future Mazur-style development, or generalized elliptic curves
at the cusps later) finding the Weierstrass-fibre formulation awkward compared to the
cohomological one, after substantial code depends on it.

**7.2 The group-law chain.** Abel via rigidified $\operatorname{Pic}^0$ with
cohomology-and-base-change as named boxes is the [KM]-faithful route, but it is the
longest prerequisite chain in the plan, and everything (torsion, level structures,
pairings) sits on it. Alternatives (fppf-sheaf-theoretic group structure; direct
chord-tangent gluing) were considered and rejected (the latter as unworkably
coordinate-heavy; the former as hiding the same cohomological content). We would value
a second opinion before committing months to this chain.

**7.3 The Weil pairing.** Construction of record undecided pending the full [KM] text
(§2.8); candidates: the norm/divisor construction, theta-group commutators, Cartier
autoduality. Also the *normalisation* (the two standard conventions differ by
inversion) must be fixed once, project-wide, and pinned by the fibrewise comparison
with the classical field-level pairing.

**7.4 $\Gamma_0(N)$ staging.** The skeleton states cyclicity via its geometric-fibre
form, with the literal fppf-local Drinfeld form as a recorded upgrade obligation. Over
geometric points the two agree; the general equivalence is exactly the delicacy [KM]
Ch. 6 handles. Is the staging acceptable, provided the fppf form becomes the
definition of record before any $\Gamma_0$-moduli theorem is stated?

**7.5 Source availability.** The project currently possesses [KM] only through
Ch. 1 §1.9. All leaves whose only source is later [KM] are explicitly gated ("cite
verbatim before proving") and worked from [Loe]/[Hida] in the interim.

## 8. Questions for the reviewer

**Q1 (definition of record).** Is Definition 4.1 — smooth proper of relative dimension
one, a section, and fibres pointed-isomorphic to plane Weierstrass models over the
residue fields, with Riemann–Roch black-boxed — an acceptable *definition of record*
for a library that will later serve Mazur-style arguments and (eventually) generalized
elliptic curves? Would you instead insist on waiting for coherent cohomology and
defining genus, accepting the delay?

**Q2 (fibre condition form).** As stated, the fibre condition is imposed at every
point via the residue field (not only at geometric points, and without passing to the
algebraic closure). Do you see arithmetic pathologies (imperfect residue fields;
non-smooth-locus subtleties) that make one of the variants (residue-field vs
geometric-fibre) strictly preferable?

**Q3 (group-law route).** Do you endorse the Abel/$\operatorname{Pic}^0$ route with
cohomology-and-base-change as named black boxes? Which precise cohomological statements
would you designate as the boxes (e.g. "$\pi_*\mathcal{O}_E=\mathcal{O}_S$ compatibly
with base change", "$R^1\pi_*\mathcal{O}_E$ is a line bundle"), so that they are stated
once and never grow?

**Q4 (registered-data discipline).** The group law, the pairing, divisor sums,
$V_{\bar\rho}$ are registered canonical data with pinning specifications (§3(i)). Do
you see a case where "unique up to the stated specification" is *not* enough — i.e.
where a later consumer will need a property of the specific construction that no
reasonable specification list would contain?

**Q5 (Weil pairing construction).** Which construction of $e_N$ over an arbitrary base
gives the most usable interface in your experience: [KM] 2.8's norm/divisor
construction, theta-group commutators (Mumford-style), or autoduality/Cartier duality?
Is there a reason to prefer one for *composite* $N$ and for compatibility
$e_{NM}\mapsto e_N$?

**Q6 (normalisation).** Which of the two standard normalisations of the Weil pairing
should be adopted (concretely: the one for which the cyclotomic-character convention
$\sigma\zeta=\zeta^{\chi(\sigma)}$ makes the determinant of the mod-$N$ representation
of an elliptic curve equal to $\chi$, i.e. Silverman III.8's convention, or its
inverse)? The choice propagates into the datum $p$ of Definition 4.6 and into the
$\bar\rho$-level pairing condition; we want to fix it once, now.

**Q7 (moduli formalism vs stacks).** For this library's goals — with Mazur's
$X_0(N)/\mathbb{Z}$ and the Shimura-surface material treated as black boxes by
consumers — is the chosen packaging (the $\mathrm{Ell}/R$ presheaf formalism as engine,
plus concrete fppf-descent statements, with fibered-category/stack packaging deferred
as a non-load-bearing bridge) mathematically honest and future-proof? Or would you
prioritise genuine algebraic-stack infrastructure now, and why?

**Q8 (staging over $\mathbb{Z}[1/N]$).** The theorem programme proves everything first
where $N$ is invertible, deferring [KM] Ch. 5–7. Which specific integral statements
will downstream consumers (Mazur-type arguments, semistable reduction bookkeeping)
force earliest, so we can order the later phases correctly?

**Q9 (the twisted curve).** For $Y(\bar\rho)$ we plan: construct $Y(N)_{\mathbb{Q}}$
with its $\mathrm{GL}_2(\mathbb{Z}/N)$-action, then Galois-descend the
$\bar\rho$-twisted form (affine invariants). Do you foresee an obstruction to getting
the *moduli interpretation* (not just the curve) through the twist — i.e. the natural
bijection between $T$-points and $\bar\rho$-level pairs $(E,\alpha)$, functorially in
the $\mathbb{Q}$-scheme $T$ — and is there a slicker route you would recommend
(e.g. representing the twisted problem directly as an open-closed piece of a Weil
restriction)?

## 9. Auxiliary remarks (appendix)

- The elementary layer (Tate normal form; the universal curve over
  $\mathbb{Z}[A,B][\Delta^{-1}]$; the explicit
  $Y_1(5)=\operatorname{Spec}\mathbb{Z}[1/5,B][\Delta(1+B,B)^{-1}]$) is deliberately
  front-loaded: it is provable with today's library, it exercises the definitions
  early, and [KM] themselves bootstrap representability through exactly such explicit
  families.
- Loeffler's supersingular caution (naive "order 5" fails in characteristic 5:
  $E[5]$ is one point with multiplicity 25) and [KM] Caution 1.4.3 are recorded next
  to the definitions they motivate, as permanent guardrails against later
  "simplifications".
- The analytic comparison ($Y(\Gamma)(\mathbb{C})\cong\Gamma\backslash\mathcal{H}$)
  is scheduled after the algebraic theory, reusing the repository's existing modular
  forms/congruence-subgroup analytic infrastructure.

## 10. Document metadata

- Project: modular curves / arithmetic moduli programme (Lean 4, one shared library).
- Brief generated: 2026-07-05. Draft pending owner sign-off of §8.
- State at time of writing: full statement scaffold compiles (73 deferred proofs; the
  data/black-box registers as in §3); no proofs beyond plumbing yet; ticket board of
  24 work + 11 cleanup tickets across 6 parallel streams.
- Requested reviewer effort: the definitions (§4) and questions (§8); §§5–7 are
  context.
