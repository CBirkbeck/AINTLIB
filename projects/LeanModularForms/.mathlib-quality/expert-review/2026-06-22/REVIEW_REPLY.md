# Reply — route analysis for the integral Hecke-algebra finiteness

*2026-06-22. **This is the agent's own best mathematical analysis**, not an external human reviewer's
reply (no external reviewer / `chatgpt-math` proxy was available). Recorded here so the decision is
auditable; replace/augment with a real expert reply if one is later obtained.*

## Headline verdict

**Build route A (modular symbols + Eichler–Shimura), but exploit the weak target: we need only the
*injectivity* of the period map, not the full Eichler–Shimura isomorphism.** This is strictly cheaper
than route B (rationality / q-expansion principle), and the Sturm-bound and "bypass-the-lattice"
shortcuts (Q4, Q5) provably do **not** work. The two genuine bottlenecks are (1) the Manin presentation
of the integral modular-symbol module and (2) injectivity of the period map.

## Answers

**Q2 first (the key economy).** FIH ($\mathbb T_{\mathbb Z}$ module-finite) follows from just three
facts, NOT the full Eichler–Shimura isomorphism:
- $\mathbb M_k(\Gamma_1(N);\mathbb Z)$ is a finite free $\mathbb Z$-module;
- the Hecke action on it is by integer matrices (Hecke-equivariant);
- the period map $\iota : S_k \to \mathbb M_k(\mathbb Z)^\vee\otimes\mathbb C$ is **Hecke-equivariant
  and injective**.

Proof that this suffices: if $T\in\mathbb T_{\mathbb Z}$ acts as $0$ on $\mathbb M_k(\mathbb Z)$, then
$T=0$ on $\mathbb M_k(\mathbb Z)^\vee\otimes\mathbb C$, so for all $f$, $\iota(Tf)=T\cdot\iota(f)=0$,
so $Tf\in\ker\iota=0$, so $T=0$ on $S_k$, so $T=0$ (the action on $S_k$ is faithful by definition of
$\mathbb T_{\mathbb Z}$). Hence $\mathbb T_{\mathbb Z}\hookrightarrow\operatorname{End}_{\mathbb Z}(\mathbb M_k(\mathbb Z))\cong M_r(\mathbb Z)$,
module-finite. **No surjectivity, no Hodge decomposition, no full-rank-in-$S_k$ needed.** This is the
same "faithful integral representation" endgame we already formalized, fed by the dual lattice instead
of an in-$S_k$ lattice.

**Q1 (cheapest route).** Given the available infrastructure (integer Fourier–Hecke action present;
modular curves absent), route A with the Q2 optimization is cheapest. Its analytic content collapses
to the single statement "a nonzero cusp form has a nonzero period," and its algebraic content
(modular symbols, finite free, integer Hecke action) is combinatorial. Route B needs the full
rationality theorem (Q3), which is strictly more.

**Q3 (is rationality independent / cheaper?).** No. Every proof of "$S_k(\Gamma_1(N))$ has an
integer-$q$-expansion basis" at general weight $k$ routes through Eichler–Shimura cohomology or the
algebraic theory of modular forms over $\mathbb Z$ (Katz). There is no self-contained
analytic/combinatorial proof reachable without that substrate. So route B is not a shortcut — it is
route A plus extra.

**Q4 (Sturm-bound shortcut).** Fails, and the failure is precise. The Sturm bound gives
$S_k\hookrightarrow\mathbb C^B$ and shows $\mathbb T_{\mathbb Z}$ is finitely generated **as a
$\mathbb Z$-algebra** (finitely many $T_p$ generate on the finite-dimensional space). But
module-finiteness additionally needs each generator $T_p$ to be **integral over $\mathbb Z$**, i.e.
the characteristic polynomial of $T_p$ on $S_k$ to have integer coefficients. The integer Fourier
recursion does **not** give this: the matrix of $T_p$ in an *arbitrary* $\mathbb C$-basis is not
integral. Integrality of $T_p$ holds iff $T_p$ preserves a full-rank integer lattice — exactly the
input we are trying to construct. So Sturm + integer recursion gives "f.g. as algebra," not "f.g. as
module"; the gap is precisely integrality, which is the lattice.

**Q5 (bypass the lattice for algebraicity / number field).** Fails for the same reason, one level
weaker. $\dim_{\mathbb C}S_k<\infty$ makes $\mathbb T_{\mathbb C}=\mathbb C\otimes\mathbb T_{\mathbb Z}$
finite-dimensional over $\mathbb C$ — but that says nothing about a $\mathbb Q$-structure. For the
eigenvalues $a_n$ to be *algebraic over $\mathbb Q$* (let alone integers), the operators must be
defined over $\overline{\mathbb Q}$, i.e. $S_k$ must carry a $\mathbb Q$-rational structure preserved
by the $T_n$ — which is rationality again. Without it, an eigenvalue of a $\mathbb C$-linear operator
on a $\mathbb C$-space could a priori be transcendental. So even the weakest target ($[K_f:\mathbb Q]<\infty$)
requires the rational structure; the $\mathbb Z$-refinement supplies the integral part. **No bypass.**

**Q6 (existing formalizations).** mathlib has only basic group (co)homology and (level-one) modular-form
dimension; no modular symbols, Eichler–Shimura, or integral Hecke algebra. No known complete
formalization of FIH in any system to import.

## Consequent plan (route A, injectivity-only)

The deep input `exists_HeckeStableLattice` is replaced by the modular-symbol package. Decomposition
leaves (to be detailed by `/develop --decompose`):

- **ES-1** $\mathbb M_k(\Gamma_1(N);\mathbb Z) := \big(\mathrm{Div}^0(\mathbb P^1(\mathbb Q))\otimes
  \operatorname{Sym}^{k-2}\mathbb Z^2\big)_{\Gamma_1(N)}$ is a finite free $\mathbb Z$-module (Manin
  presentation: generators over $\Gamma_1(N)\backslash\mathrm{SL}_2(\mathbb Z)\times$ a basis of
  $\operatorname{Sym}^{k-2}$, with 2-term/3-term/parabolic relations). *Combinatorial.* Needs:
  $\operatorname{Sym}^{k-2}\mathbb Z^2$, $\mathbb P^1(\mathbb Q)$, the $\mathrm{SL}_2$-action,
  $\mathrm{Div}^0$, group coinvariants ($H_0$).
- **ES-2** Hecke ($T_n, U_p, \langle d\rangle$) acts on $\mathbb M_k(\mathbb Z)$ by integer (Heilbronn)
  matrices; Hecke-equivariant. *Combinatorial.* Depends ES-1.
- **ES-3** the period map $\iota : S_k \to \mathbb M_k(\mathbb Z)^\vee\otimes\mathbb C$,
  $\langle f,\{\alpha,\beta\}\otimes P\rangle=\int_\alpha^\beta f(z)P(z,1)\,dz$, is well-defined
  (convergence via cusp decay), descends to $\mathbb M_k$, and is Hecke-equivariant. *Analytic.*
- **ES-4** $\iota$ is **injective** (a nonzero cusp form has a nonzero period). *Analytic — the genuine
  core.* Depends ES-3.
- **ES-asm** assemble FIH from ES-1/2/4 via the Q2 faithfulness argument. *Bounded* (we have the
  `End_ℤ`/`of_injective` machinery; adapt the proven endgame to the dual lattice).

Foundational tractable starting points (where mathlib gives the most): the abstract
modular-symbol module and its finite-generation (ES-1) — group coinvariants + $\operatorname{Sym}^{k-2}$;
and ES-asm (the faithfulness endgame, adapting the existing proof). ES-3/ES-4 (the period integral and
its injectivity) are the analytic heart and the highest-risk leaves.
