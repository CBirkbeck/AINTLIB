# Review brief — Atkin–Lehner Main Lemma (Γ₁(N)) and linear independence of Hecke eigensystems

*Prepared 2026-06-17 for a senior expert in modular forms / Hecke theory. Self-contained: no repository access required. This concerns a formal (machine-checked) development, but every question below is ordinary mathematics — the formalization details are suppressed.*

---

## 1. Goal

We are formalizing classical newform theory for $\Gamma_1(N)$ — Hecke operators, eigenforms, strong multiplicity one, the old/new decomposition, and the **Atkin–Lehner Main Lemma** — as the backbone for a verified construction of **LMFDB-style labels** of classical modular newforms. Strong multiplicity one and the *per-character* Main Lemma are already complete and machine-checked. The one remaining gap in the Main Lemma is its **global ($\Gamma_1(N)$, all nebentypus at once) form**, and that gap has been isolated to a single statement about **linear independence of distinct systems of Hecke eigenvalues**. The brief asks whether that statement has a proof that does *not* implicitly assume the Main Lemma itself.

---

## 2. Background and references

### 2.1 Setting and conventions

Fix an integer weight $k \ge 2$ and a level $N \ge 1$. Write $S_k(\Gamma_1(N))$ for the space of weight-$k$ cusp forms on $\Gamma_1(N)$, and for a Dirichlet character $\chi \bmod N$ write $S_k(N,\chi)$ for the $\chi$-nebentypus subspace, so that
$$ S_k(\Gamma_1(N)) \;=\; \bigoplus_{\chi \bmod N} S_k(N,\chi), $$
where the diamond operator $\langle d\rangle$ acts on $S_k(N,\chi)$ by the scalar $\chi(d)$, for $d \in (\mathbb{Z}/N)^\times$.

For $n \ge 1$ let $T_n$ denote the $n$-th Hecke operator. We are interested throughout in the operators $T_n$ with $\gcd(n,N)=1$ (the "good", or "prime-to-level", Hecke operators); these commute with one another and with the diamond operators, and are self-adjoint up to the diamond twist for the Petersson inner product. We write $q$-expansions at $\infty$ as $f = \sum_{n\ge 1} a_n(f)\,q^n$ (period $1$; $a_0 = 0$ for cusp forms).

We use the standard prime-power Hecke recursion, in its operator form on $S_k(\Gamma_1(N))$: for a prime $p \nmid N$,
$$ T_{p^{r+2}} \;=\; T_p\,T_{p^{r+1}} \;-\; p^{k-1}\,\langle p\rangle\,T_{p^{r}}\qquad(r\ge 0), \tag{R}$$
and $T_m T_{m'} = T_{mm'}$ for $\gcd(m,m')=1$. In particular $T_p^2 = T_{p^2} + p^{k-1}\langle p\rangle$.

By a *common Hecke eigenform* (for the good operators) we mean a nonzero $f$ with $T_n f = \lambda_n f$ for all $n$ coprime to $N$; its **eigensystem** is the function $\mathrm{ev}_f : \{n : \gcd(n,N)=1\} \to \mathbb{C}$, $\mathrm{ev}_f(n) = \lambda_n$. Note $\mathrm{ev}_f$ is multiplicative on coprime arguments ($\mathrm{ev}_f(mm') = \mathrm{ev}_f(m)\mathrm{ev}_f(m')$ for $\gcd(m,m')=1$) but **not** completely multiplicative — by (R) the prime-power values satisfy a degree-two recursion involving $\chi(p)$, not $\mathrm{ev}_f(p)^r$.

For a common eigenform $f$ in a single nebentypus space one has the standard relation
$$ a_n(f) \;=\; \mathrm{ev}_f(n)\,a_1(f)\qquad(\gcd(n,N)=1). \tag{E}$$

The **old subspace** $S_k(\Gamma_1(N))^{\mathrm{old}}$ is spanned by the images of $S_k(\Gamma_1(M))$ for proper divisors $M \mid N$ under the degeneracy maps $f(z) \mapsto f(dz)$, $d \mid N/M$.

### 2.2 References

- **[DS05]** Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in Mathematics 228, Springer, 2005. (Newform theory, Chapter 5; the "Main Lemma" is Theorem 5.7.1; old/new decomposition §5.6; multiplicity one §5.8.)
- **[Miyake]** Toshitsune Miyake, *Modular Forms*, Springer Monographs in Mathematics, Springer, 2006. (Hecke theory and the sieve argument for the Main Lemma, §4.6.)
- **[AL70]** A. O. L. Atkin and J. Lehner, "Hecke operators on $\Gamma_0(m)$", *Mathematische Annalen* 185 (1970), 134–160.
- **[Li75]** Wen-Ch'ing Winnie Li, "Newforms and functional equations", *Mathematische Annalen* 212 (1975), 285–315. (Newform theory with nebentypus; multiplicity one and strong multiplicity one in the $\Gamma_1(N)$ setting.)

### 2.3 State of the art (within the formalization)

Already machine-checked and axiom-clean in our development:

- **Strong multiplicity one** (the statement that a normalized newform is determined by its prime-to-level Hecke eigenvalues), proven via a per-character route.
- The **per-character Main Lemma**: *if $f \in S_k(N,\chi)$ has $a_n(f) = 0$ for all $n$ coprime to $N$, then $f$ is old* — established via Miyake's §4.6 sieve / conductor descent.
- The Petersson product, self-adjointness of the good Hecke operators (up to the diamond twist), and the resulting simultaneous diagonalizability / joint-eigenspace decomposition of $S_k(\Gamma_1(N))$ under the good Hecke operators.
- Two ingredients of the global reduction described in §3 below: the eigenvalue–coefficient identity (E), and the fact (call it L2) that *the prime-to-level eigensystem determines the nebentypus* — for a common eigenform $f \in S_k(N,\chi)$ and a prime $p\nmid N$, (R) gives $\chi(p) = p^{1-k}\big(\mathrm{ev}_f(p)^2 - \mathrm{ev}_f(p^2)\big)$, and $\chi$ is then pinned down on all of $(\mathbb{Z}/N)^\times$ by multiplicativity.

The one open piece is the **global Main Lemma** and, after the reduction in §3, the single statement **L3** in §8.

---

## 3. Strategy and the reduction

**Target (global Main Lemma).** *If $f \in S_k(\Gamma_1(N))$ satisfies $a_n(f) = 0$ for all $n$ coprime to $N$, then $f \in S_k(\Gamma_1(N))^{\mathrm{old}}$.*

We attempted to reduce this to the (proven) per-character version **spectrally**, as follows. Decompose $f$ into joint eigenspaces of the good Hecke operators,
$$ f \;=\; \sum_{i} f_i, \qquad f_i \in (\text{joint eigenspace with eigensystem } \mathrm{ev}_i), $$
with the $\mathrm{ev}_i$ pairwise distinct. Each joint eigenspace lies in a single nebentypus space (the diamond eigenvalues are part of the joint eigensystem, and are recovered from the prime-to-level data by L2), so each $f_i \in S_k(N,\chi_i)$ for a well-defined $\chi_i$. By (E),
$$ a_n(f) \;=\; \sum_i \mathrm{ev}_i(n)\,a_1(f_i)\qquad(\gcd(n,N)=1). $$
The hypothesis $a_n(f) = 0$ for all coprime $n$ thus reads
$$ \sum_i a_1(f_i)\,\mathrm{ev}_i(n) \;=\; 0 \qquad\text{for all } n \text{ coprime to } N. \tag{$\star$}$$
If we knew **linear independence of the distinct eigensystems** (statement L3 below), then ($\star$) would force $a_1(f_i) = 0$ for every $i$; by (E), $a_n(f_i)=0$ for all coprime $n$; each $f_i$ then has vanishing prime-to-level coefficients and lies in a single nebentypus space, so the **per-character Main Lemma** makes each $f_i$ old, whence $f = \sum_i f_i$ is old. $\square$

So the global Main Lemma follows from the per-character one **plus** the following purely algebraic-looking statement.

---

## 4. The key statement

> **L3 (linear independence of Hecke eigensystems).** Let $f_1,\dots,f_r$ be common Hecke eigenforms (for the good operators) in $S_k(\Gamma_1(N))$, each nonzero, with pairwise distinct eigensystems $\mathrm{ev}_1,\dots,\mathrm{ev}_r$ (i.e. for $i\ne j$ there is some $n$ coprime to $N$ with $\mathrm{ev}_i(n)\ne\mathrm{ev}_j(n)$). Suppose $c_1,\dots,c_r \in \mathbb{C}$ satisfy
> $$ \sum_{i=1}^{r} c_i\,\mathrm{ev}_i(n) \;=\; 0 \qquad\text{for all } n \text{ coprime to } N. $$
> Then $c_1 = \dots = c_r = 0$.

Equivalently: the $r$ functions $n \mapsto \mathrm{ev}_i(n)$ (on the prime-to-$N$ positive integers) are $\mathbb{C}$-linearly independent. Note the relation is imposed only at arguments coprime to $N$ (equivalently, only against the good Hecke operators $T_n$).

This is "obviously true" — it is the standard fact that distinct Hecke eigenforms are linearly independent — but the question is **whether it can be proved without first knowing the Main Lemma**, since here it is being used to *prove* the Main Lemma.

---

## 5. Established results used above

- **(E) Eigenvalue–coefficient identity.** For a common eigenform $f$ in a single nebentypus space and $\gcd(n,N)=1$: $a_n(f) = \mathrm{ev}_f(n)\,a_1(f)$. *(Standard; $a_n(f) = a_1(T_n f) = \mathrm{ev}_f(n)\,a_1(f)$.)*
- **(L2) Eigensystem determines nebentypus.** Two nonzero common eigenforms with equal prime-to-level eigensystems lie in the same nebentypus space. *(From (R): $\chi(p)$ is recovered as $p^{1-k}(\mathrm{ev}(p)^2 - \mathrm{ev}(p^2))$ for each $p\nmid N$, and $\chi$ is determined by its values on primes.)*
- **Joint-eigenspace decomposition.** $S_k(\Gamma_1(N))$ is the orthogonal direct sum of the joint eigenspaces of the good Hecke operators. *(Self-adjointness up to diamond twist; finite dimension; commuting family.)*
- **Per-character Main Lemma.** As in §2.3.

---

## 6. In progress

**Global Main Lemma** (the §3 target). Status: reduced, as in §3, to **L3** alone; everything else in the reduction is machine-checked. We have a complete formal proof modulo a single unproved lemma whose statement is exactly L3.

---

## 7. Targets

The global Main Lemma is, in our development, currently **without downstream consumers**: the labeling machinery and strong multiplicity one rely only on the per-character Main Lemma. So completing the global version is a matter of mathematical completeness rather than unblocking other work — which is why we want to know the *cost* of doing it honestly before committing to it.

---

## 8. Where we are stuck — the suspected circularity of L3

We could not find a proof of **L3** that avoids the Main Lemma, and we have a fairly precise reason to suspect there isn't an easy one. We would like this either confirmed or refuted.

**8.1 The natural "spectral/Dedekind" proof, and why it stalls.** The eigensystems $\mathrm{ev}_i$ are the characters (algebra homomorphisms to $\mathbb{C}$) of the commutative Hecke algebra $\mathbb{T} \subseteq \mathrm{End}(S_k(\Gamma_1(N)))$ generated by the good operators. Because the good operators are self-adjoint (up to twist) and commute, $\mathbb{T}$ is semisimple, so its distinct characters are linearly independent **as functionals on all of $\mathbb{T}$**. That is exactly Dedekind/Artin independence of characters — and it would give L3 *if the relation in L3 were imposed on all of $\mathbb{T}$.* But the relation is imposed only against the **generators** $\{T_n : \gcd(n,N)=1\}$, and these do **not linearly span** $\mathbb{T}$: by the recursion (R), $T_p^2 = T_{p^2} + p^{k-1}\langle p\rangle$, so products of good operators immediately produce the **diamond operators** $\langle p\rangle$, which are *not* in the linear span of $\{T_n\}$. A linear relation $\sum_i c_i\,\mathrm{ev}_i$ that vanishes on $\{T_n\}$ therefore vanishes only on the proper subspace $\mathrm{span}\{T_n\}\subsetneq\mathbb{T}$, and the restrictions of distinct characters to a proper subspace need not be independent. There is no *linear* way to recover the diamond values from the relation, since $\chi_i(p) = p^{1-k}(\mathrm{ev}_i(p)^2 - \mathrm{ev}_i(p^2))$ is **quadratic** in the eigenvalues.

**8.2 The "form" proof is circular.** The clean textbook proof of L3 normalizes (assume $a_1(f_i)=1$, so $a_n(f_i)=\mathrm{ev}_i(n)$) and forms $\Psi = \sum_i c_i f_i$; then $a_n(\Psi) = \sum_i c_i\,\mathrm{ev}_i(n) = 0$ for all coprime $n$, i.e. $\Psi$ has vanishing prime-to-level coefficients. One concludes $\Psi$ is **old**, and — if the $f_i$ are newforms — that $\Psi$, being simultaneously new and old, vanishes, whence $c=0$ by linear independence of the forms. But "$\Psi$ has vanishing prime-to-level coefficients $\Rightarrow$ $\Psi$ is old" **is the Main Lemma**. So this route proves L3 *from* the Main Lemma — useless for our purpose of proving the Main Lemma *from* L3.

**8.3 Other attempts.** (i) Dedekind's independence-of-characters lemma in its monoid-hom form needs the $\mathrm{ev}_i$ to be *completely* multiplicative; they are only multiplicative on coprime arguments, and indeed three *merely* multiplicative functions agreeing off one prime $p$ and taking values $1,2,3$ at $p$ and $5,7,9$ at $p^2$ satisfy $f_1 - 2f_2 + f_3 = 0$ — so multiplicativity alone is genuinely insufficient, and the recursion (R) (equivalently: the $\chi_i(p)$ are roots of unity) is essential to the truth of L3. (ii) Orthogonality of the eigenforms gives linear independence of the *forms* $f_i$, but not of the eigenvalue *functions* $\mathrm{ev}_i$ — these are different statements, and in fact the prime-to-level coefficient sequences of independent forms need *not* be independent (degeneracy lifts $f(dz)$, $d\mid N$, $d>1$, have *vanishing* prime-to-level coefficients). (iii) Recovering the diamonds via (R) reintroduces the Main Lemma or requires controlling quadratic expressions $\sum_i c_i\,\mathrm{ev}_i(p)^2$ that the linear relation does not see.

**8.4 The apparent dichotomy.** Every route we tried either (a) requires the relation on operators outside $\mathrm{span}\{T_n\}$ (the diamonds), which the hypothesis does not provide, or (b) invokes "vanishing prime-to-level coefficients $\Rightarrow$ old", i.e. the Main Lemma. This makes L3 *look* inter-reducible with the global Main Lemma. The only route we can see that is definitely non-circular is to **re-prove the Main Lemma directly and globally** by running Miyake's §4.6 sieve / conductor descent on $\Gamma_1(N)$ with the diamond operator $\langle d\rangle$ in place of the scalar $\chi(d)$ — a substantial undertaking we would rather avoid if L3 has an independent proof.

---

## 9. Questions for the reviewer

**Q1.** Is **L3** — $\mathbb{C}$-linear independence of finitely many distinct prime-to-level Hecke eigensystems, with the linear relation imposed *only* at arguments coprime to $N$ — provable **without** assuming the statement "a cusp form with vanishing prime-to-level coefficients is old" (the Main Lemma)? Or is it genuinely inter-reducible with it?

**Q2.** If it is provable independently, what is the cleanest argument? In particular, is there a standard route via (a) the multiplicity-one / newform theory of [Li75] that does *not* secretly use the Main Lemma, (b) an $L$-function / Rankin–Selberg nonvanishing argument (distinct eigensystems give distinct $L$-functions; can one extract independence at the level of the Dirichlet coefficients without the old/new dictionary?), or (c) a direct argument with the recursion (R) showing that the prime-to-level operators already span $\mathbb{T}$ in a way that I am missing? A reference would be ideal.

**Q3.** Is it correct that the obstruction is exactly "$\{T_n : \gcd(n,N)=1\}$ do not linearly span the Hecke algebra (the diamonds escape via (R))," and hence that whether the *restrictions* of the characters to $\mathrm{span}\{T_n\}$ remain independent is precisely the content of L3 — i.e. that semisimplicity of $\mathbb{T}$ alone cannot give it? If so, is there nonetheless a soft reason (e.g. the prime-to-level eigensystem determining the full eigensystem via (R), §5 L2) that forces the restricted characters to stay independent?

**Q4.** Strategic: given that the *global* Main Lemma currently has no downstream consumers in our development (everything uses the per-character version), and that the honest fallback is a full character-free re-run of the §4.6 sieve, would you regard the global statement as worth the cost — or is the per-character Main Lemma the natural stopping point, with the $\Gamma_1(N)$ statement recorded as a routine-but-laborious corollary?

---

## 10. Document metadata

- Project: formalized newform theory toward LMFDB labels (component: Atkin–Lehner Main Lemma).
- Brief generated: 2026-06-17.
- Status at time of writing: the global Main Lemma compiles modulo exactly one unproved lemma (L3); strong multiplicity one and the per-character Main Lemma are complete and axiom-clean.
- Length: ~4 pages.
