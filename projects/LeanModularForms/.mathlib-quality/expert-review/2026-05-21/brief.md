# Review brief — Hecke operators as a commutative algebra acting on modular forms with nebentypus

*Prepared 2026-05-21 for an AI mathematical reviewer. Self-contained: no repository or code access required. All notation is defined below; no programming content appears.*

## 1. Goal

We are formalising classical Hecke theory for holomorphic modular forms. We have, on one hand, the **abstract Hecke ring** $\mathbb{T}(\Gamma_0(N))$ of double cosets with its convolution product, proven commutative; and on the other, a family of **concrete Hecke operators** $T_n$ acting on spaces of modular forms. These were developed as two independent tracks. We now want to connect them through **ring homomorphisms from the Hecke ring into the endomorphism algebra** of the relevant modular-form space, and then use those homomorphisms as the primary interface throughout — so that commutativity and multiplicativity of Hecke operators become corollaries of the algebra structure rather than separately-proven facts.

The immediate milestone, and the subject of this brief, is to construct such a ring homomorphism **landing in the space of modular forms with a fixed nebentypus character $\chi$** — i.e. into $\operatorname{End}_{\mathbb{C}}\!\big(M_k(\Gamma_1(N),\chi)\big)$ — for **arbitrary** $\chi$. We have it for trivial $\chi$, and we have a general-$\chi$ version landing in a larger *function* space; the gap is landing it in the genuine (holomorphic, cusp-bounded) nebentypus space.

## 2. Background and references

### 2.1. Setting

Fix an integer level $N \ge 1$ and an integer weight $k$. Write $\Gamma_1(N) \subseteq \Gamma_0(N) \subseteq \mathrm{SL}_2(\mathbb{Z})$ for the usual congruence subgroups, and $\mathbb{H}$ for the upper half-plane.

- **Weight-$k$ slash action.** For $g \in \mathrm{GL}_2^+(\mathbb{R})$, $g = \begin{pmatrix} a&b\\ c&d\end{pmatrix}$, and $f:\mathbb{H}\to\mathbb{C}$, we write $f\big|_k g$ for the standard weight-$k$ action $(f|_k g)(z) = (\det g)^{k-1}(cz+d)^{-k} f(gz)$. (The determinant normalisation is fixed throughout and matches the convention under which Hecke operators have integer-indexed eigenvalue recursions.)

- **Modular forms.** $M_k(\Gamma)$ is the space of holomorphic functions on $\mathbb{H}$ that are weight-$k$ invariant under $\Gamma$ and holomorphic (bounded) at every cusp; $S_k(\Gamma)$ the subspace vanishing at all cusps.

- **Diamond operators.** For $d \in (\mathbb{Z}/N)^\times$, the diamond operator $\langle d\rangle$ on $M_k(\Gamma_1(N))$ is defined by choosing any $\gamma \in \Gamma_0(N)$ whose lower-right entry reduces to $d$ modulo $N$ and setting $\langle d\rangle f = f|_k\gamma$. This is well-defined (independent of the representative) because two such representatives differ by an element of $\Gamma_1(N)$, under which $f$ is invariant. The assignment $d \mapsto \langle d\rangle$ is a homomorphism $(\mathbb{Z}/N)^\times \to \operatorname{End}_{\mathbb{C}} M_k(\Gamma_1(N))$.

- **Nebentypus character spaces.** For a Dirichlet character $\chi: (\mathbb{Z}/N)^\times \to \mathbb{C}^\times$, define
$$M_k(\Gamma_1(N),\chi) \;=\; \{\, f \in M_k(\Gamma_1(N)) : \langle d\rangle f = \chi(d)\, f \ \text{for all } d \,\}, $$
the simultaneous $\chi$-eigenspace of the diamond operators, and $S_k(\Gamma_1(N),\chi)$ analogously for cusp forms. Equivalently, $f \in M_k(\Gamma_1(N),\chi)$ iff $f|_k\gamma = \chi(d_\gamma)\,f$ for all $\gamma \in \Gamma_0(N)$, where $d_\gamma$ is the lower-right entry of $\gamma$ mod $N$.

- **Abstract Hecke ring.** For the Hecke pair $(\Gamma_0(N), \Delta)$ — with $\Delta$ the relevant multiplicative monoid of integer matrices of positive determinant — $\mathbb{T}(\Gamma_0(N))$ denotes the free $\mathbb{Z}$-module on the double cosets $\Gamma_0(N)\backslash\Delta/\Gamma_0(N)$, with the standard Hecke convolution product. We write $T(D)$ for the basis element of a double coset $D$.

- **Concrete Hecke operators.** A double coset $D = \bigsqcup_i \Gamma_0(N)\,\alpha_i$ acts on modular forms by $T(D)f = \sum_i f|_k\alpha_i$ (up to the fixed determinant normalisation). The classical operators $T_n$ (and $U_p$ for $p \mid N$) are these operators for the standard double cosets.

### 2.2. References

- **[Shimura 1971]** Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton Univ. Press, 1971. §3.4 develops the Hecke ring; Proposition 3.8 gives commutativity via an anti-involution; Proposition 3.30 gives that the double-coset action is a (anti-)homomorphism; Proposition 3.35 relates the abstract ring product to operator composition.
- **[Diamond–Shurman 2005]** Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, GTM 228, Springer, 2005. §5.2 develops Hecke and diamond operators on $M_k(\Gamma_1(N))$; Proposition 5.2.1 gives the commutation $T_p\langle d\rangle = \langle d\rangle T_p$ and the nebentypus decomposition.
- **[Miyake 1989]** Toshitsune Miyake, *Modular Forms*, Springer, 1989. §4.5 (coset representatives for the Hecke action) and §4.6 (newform / multiplicity-one theory).

### 2.3. State of the art

This is entirely classical mathematics; the content of the milestone is a formalisation/organisation question, not new theorems. The standard references construct Hecke operators on $M_k(\Gamma_1(N),\chi)$ directly and obtain commutativity from the algebra. Our formalisation has the algebra and the operators but built them separately, and has the algebra-to-operator bridge only for trivial nebentypus.

## 3. Strategy

The intended end state is: Hecke operators on $M_k(\Gamma_1(N),\chi)$ are *defined as* (or are *provably equal to*) the image of the commutative Hecke ring $\mathbb{T}(\Gamma_0(N))$ under a ring homomorphism
$$\Phi_\chi : \mathbb{T}(\Gamma_0(N)) \longrightarrow \operatorname{End}_{\mathbb{C}}\!\big(M_k(\Gamma_1(N),\chi)\big),$$
so that $T_m T_n = T_n T_m$ and the multiplicativity relations follow from $\Phi_\chi$ being a homomorphism out of a commutative ring. The plan in stages:

1. **Construct $\Phi_\chi$** for arbitrary $\chi$ (this brief's milestone).
2. **Bridge:** prove the existing concrete operators $T_n$ equal $\Phi_\chi(T(D_n))$, so the algebra's relations transfer to them.
3. **Collapse:** re-derive the operator commutativity/multiplicativity (currently standalone combinatorial proofs) as corollaries of $\Phi_\chi$.
4. **Consume:** rephrase downstream eigenform theory and the multiplicity-one argument through $\Phi_\chi$.

We have already carried out the analogue of stages 1–3 for **trivial** $\chi$.

## 4. Definitions specific to the construction

- **$\chi$-twisted invariant function space.** For a Dirichlet character $\chi$ (viewed on $\Gamma_0(N)$ via the lower-right entry), let
$$V_\chi \;=\; \{\, f : \mathbb{H}\to\mathbb{C} \ \text{(no regularity assumed)} : f|_k\gamma = \chi(d_\gamma)\,f \ \text{for all } \gamma\in\Gamma_0(N)\,\}.$$
This is a $\mathbb{C}$-vector space of functions; $M_k(\Gamma_1(N),\chi)$ is exactly the subspace of $V_\chi$ consisting of functions that are additionally holomorphic on $\mathbb{H}$ and bounded at the cusps.

- **The Hecke double-coset endomorphism.** For a double coset $D$ with representatives $\{\alpha_i\}$, the operator $T(D): f \mapsto \sum_i f|_k\alpha_i$ is defined on functions and preserves both $V_\chi$ (the twisted-invariance) — *this is the equivariance fact at issue* — and, separately, holomorphy and cusp-boundedness.

## 5. Established results

**Result 5.1 (Commutativity of the Hecke ring).** *$\mathbb{T}(\Gamma_0(N))$ is a commutative ring.*

*Sketch.* An anti-involution of the Hecke pair (induced by matrix transposition / the Atkin–Lehner involution) fixes every double coset; Shimura's Proposition 3.8 then forces the convolution product to be commutative. ∎

**Result 5.2 (Level-1 and $\Gamma_0(N)$ ring homomorphisms).** *There are ring homomorphisms $\mathbb{T}(\mathrm{SL}_2(\mathbb{Z})) \to \operatorname{End}\,M_k(\mathrm{SL}_2(\mathbb{Z}))$ and $\mathbb{T}(\Gamma_0(N)) \to \operatorname{End}\,M_k(\Gamma_0(N))$, each sending $T(D)$ to the double-coset operator.*

*Sketch.* The double-coset operators compose according to the convolution product (Shimura Prop 3.30); commutativity of the source (Result 5.1) turns the resulting anti-homomorphism into a homomorphism. Extend $\mathbb{Z}$-linearly over the free module. ∎

**Result 5.3 (Trivial-nebentypus character-space homomorphism).** *There is a ring homomorphism $\mathbb{T}(\Gamma_0(N)) \to \operatorname{End}\,M_k(\Gamma_1(N),\mathbf{1})$.*

*Sketch.* $M_k(\Gamma_1(N),\mathbf{1}) \cong M_k(\Gamma_0(N))$ via a linear isomorphism; conjugate the $\Gamma_0(N)$ homomorphism of Result 5.2 through it. ∎

**Result 5.4 (General-$\chi$ homomorphism into the function space).** *For arbitrary $\chi$, there is a ring homomorphism $\mathbb{T}(\Gamma_0(N)) \to \operatorname{End}(V_\chi)$ sending $T(D)$ to the double-coset operator on the twisted-invariant function space $V_\chi$.*

*Sketch.* On $V_\chi$ (functions, no regularity), the double-coset operator preserves the twisted invariance directly, and the composition law / commutativity give the homomorphism property. ∎

**Result 5.5 (Modularity is preserved, for any double coset).** *For any double coset $D$ and any $f \in M_k(\Gamma_1(N))$, the function $T(D)f$ is holomorphic on $\mathbb{H}$ and bounded at every cusp; moreover it can be packaged as a genuine modular form, and lies in $M_k(\Gamma_1(N),\chi)$ provided the nebentypus relation below holds.*

*Sketch.* Holomorphy and cusp-boundedness of a finite sum of slashes of a modular form are routine and already established for general $D$ (independent of $\chi$). ∎

## 6. In progress — the milestone

**Construct $\Phi_\chi : \mathbb{T}(\Gamma_0(N)) \to \operatorname{End}\,M_k(\Gamma_1(N),\chi)$ for general $\chi$.**

Status: every ingredient is in place except one equivariance fact (§8.1). Concretely, given that fact, the construction is:

1. Define $\Phi_\chi(T(D))$ as the double-coset operator, with codomain restricted to $M_k(\Gamma_1(N),\chi)$ (using Result 5.5 for holomorphy/boundedness and §8.1 for the nebentypus relation).
2. Extend $\mathbb{Z}$-linearly to all of $\mathbb{T}(\Gamma_0(N))$.
3. The homomorphism property ($\Phi_\chi(D_1 D_2) = \Phi_\chi(D_1)\Phi_\chi(D_2)$) follows from the double-coset composition law plus commutativity of the source (as in Result 5.2).

## 7. Targets (after the milestone)

- The **bridge** $T_n = \Phi_\chi(T(D_n))$ identifying the standard concrete operators with the algebra image (general $n$, general $\chi$, including primes $p \mid N$).
- **Collapsing** the standalone proofs of operator commutativity and multiplicativity into corollaries of $\Phi_\chi$.
- Routing the **newform / strong-multiplicity-one** development through $\Phi_\chi$.

## 8. Where we're stuck

**Stuck point 8.1 — the nebentypus equivariance of the Hecke operator output.**

We need: for $f \in M_k(\Gamma_1(N),\chi)$ and any Hecke double coset $D$,
$$\big(T(D)f\big)\big|_k\gamma \;=\; \chi(d_\gamma)\cdot T(D)f \qquad \text{for all } \gamma \in \Gamma_0(N),$$
i.e. $T(D)f$ again satisfies the nebentypus relation, hence lies in $M_k(\Gamma_1(N),\chi)$. Equivalently, this is the statement that the Hecke operators **commute with the diamond operators** ($T(D)\langle d\rangle = \langle d\rangle T(D)$), restricted to the $\chi$-eigenspace (Diamond–Shurman Prop 5.2.1).

What we have:

- For **trivial** $\chi$ (the invariance $T(D)f|_k\gamma = T(D)f$) this is proven.
- The modularity packaging (holomorphy, cusp-boundedness, assembling a modular form, membership in the $\chi$-space) is **fully proven for general $D$ and takes this equivariance as a hypothesis** — so once 8.1 is supplied, the milestone closes mechanically.
- There is an *independent* general-$\chi$ homomorphism into the **function** space $V_\chi$ (Result 5.4), but its target carries no holomorphy/cusp data, and we have **not** established that $V_\chi \cap \{\text{holomorphic, cusp-bounded}\}$ is literally $M_k(\Gamma_1(N),\chi)$ in a way that transports that homomorphism — the two invariance encodings (a twisted slash fixed-point condition vs. a diamond-eigenvalue condition) have not been identified.

The classical argument (DS Prop 5.2.1) tracks how right-multiplication by $\gamma \in \Gamma_0(N)$ permutes the coset representatives $\{\alpha_i\}$ of $D$, with the determinant/lower-right character producing the factor $\chi(d_\gamma)$. The remaining work is exactly this matrix bookkeeping for general $\chi$ — believed to be on the order of one to two weeks of formalisation, and the only mathematical content left in the milestone.

**Stuck point 8.2 — the right organising principle for the refactor.**

We want the construction to be the one a careful textbook would choose, both for cleanliness now and for reuse across the project. Specifically we are unsure (i) whether to base everything on the **$\Gamma_0(N)$** Hecke ring acting with the $\chi$-twist (which is already commutative) or to introduce a genuine **$\Gamma_1(N)$** Hecke ring; (ii) whether to prove 8.1 directly or to instead invest in identifying the holomorphic part of $V_\chi$ with $M_k(\Gamma_1(N),\chi)$ and transporting Result 5.4; and (iii) how to handle the operators at primes $p \mid N$ (the $U_p$) within the same uniform double-coset framework.

## 9. Open mathematical questions for the reviewer

**Q1 (how to structure the refactor).** Given a commutative Hecke ring and a separately-built family of concrete Hecke operators, what is the cleanest way to organise "Hecke operators as the image of a ring homomorphism into endomorphisms of $M_k(\Gamma_1(N),\chi)$"? In particular: should the homomorphism's source be $\mathbb{T}(\Gamma_0(N))$ acting with the nebentypus twist (we believe this is standard and avoids needing a separate $\Gamma_1(N)$ Hecke ring), or is there a reason to prefer a genuine $\Gamma_1(N)$ Hecke algebra? Is the bridge "$T_n = \Phi_\chi(T(D_n))$" best proven coset-by-coset, or via a generators-and-relations / universal-property argument on $\mathbb{T}$?

**Q2 (how to land the map in the $\chi$-spaces — the blocker 8.1).** What is the cleanest route to the nebentypus equivariance $(T(D)f)|_k\gamma = \chi(d_\gamma)\,T(D)f$ for general $\chi$? Is the representative-permutation/determinant-character argument of Diamond–Shurman Prop 5.2.1 the right one to formalise, and are there pitfalls at primes dividing $N$? Alternatively, is it cleaner to **avoid** re-proving it by establishing that the holomorphic, cusp-bounded part of the twisted-invariant function space $V_\chi$ *is* $M_k(\Gamma_1(N),\chi)$, and transporting the function-level homomorphism (Result 5.4) — i.e., is the diamond-eigenspace description and the twisted-slash fixed-point description interchangeable in a way that makes the modularity transport automatic?

**Q3 (generality of the source ring).** Is it correct and standard that the **same** commutative ring $\mathbb{T}(\Gamma_0(N))$ acts on every nebentypus eigenspace $M_k(\Gamma_1(N),\chi)$ simultaneously (the $\chi$ entering only through the action, not the ring)? We want to confirm we are not missing a subtlety that would force a $\chi$-dependent or $\Gamma_1(N)$-level Hecke algebra.

**Q4 (operators at bad primes).** For $p \mid N$, the operator $U_p$ arises from a different double coset and is not normal/self-adjoint in the usual sense. Does the equivariance argument of Q2, and the homomorphism property generally, go through uniformly for these double cosets, or do they require separate handling within the construction?

**Q5 (is this the right interface to commit to?).** Stepping back: for a library intended to support newform theory and multiplicity-one, is "ring homomorphism from $\mathbb{T}(\Gamma_0(N))$ into $\operatorname{End}\,M_k(\Gamma_1(N),\chi)$" the right primary abstraction to build everything on — or would the reviewer organise the Hecke action differently (e.g. as a single action of one big algebra on the sum over all $\chi$, or via the Hecke algebra acting on $M_k(\Gamma_1(N))$ with the nebentypus decomposition derived afterwards)?

## 10. Document metadata

- Project: formalisation of classical Hecke theory and strong multiplicity one for holomorphic modular forms.
- Brief generated: 2026-05-21.
- Length: ~4 pages.
- Build status: the established results (§5) all compile; the milestone (§6) and targets (§7) are not yet built. The downstream multiplicity-one theorem is proven independently and is axiom-clean.
- Recent context: the two tracks (abstract Hecke ring; concrete operators) were developed separately by design; this milestone begins joining them.
