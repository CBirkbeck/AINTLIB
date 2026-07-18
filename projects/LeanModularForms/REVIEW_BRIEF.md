# Follow-up review brief — Hecke-eigenvalue arithmetic of newforms (round 2)

*Prepared 2026-06-24, a follow-up to the 2026-06-19 brief and your reply of the same date. For the
same reviewer; self-contained, but written assuming you recall the earlier exchange. We took your
advice and built the route you recommended; this brief reports where it landed and asks the precise
next question, which is the formalize-vs-cite decision your reply explicitly deferred.*

---

## 0. What we did with your last reply

Your 2026-06-19 verdict: **do not** build a full-rank $q$-expansion lattice inside $S_k(\Gamma_1(N))$
or an integral model of $X_1(N)$ for the eigenvalue-arithmetic goals; instead build a **finite
integral modular-symbol Hecke module** $H_{\mathbb{Z}}$ together with an **injective**,
Hecke-equivariant period map $S_k(\Gamma_1(N)) \hookrightarrow H_{\mathbb{Z}}\otimes\mathbb{C}$ — the
"IHR" (integral Hecke realization) — and isolate, as the atomic library-facing input, the **(FIH)**:
the integral Hecke algebra $\mathbb{T}_{\mathbb{Z}} \subseteq \operatorname{End}_{\mathbb{C}}(S_k)$ is
a finite $\mathbb{Z}$-module. We adopted this in full. **Completed since:**

- **(FIH)** installed as the atomic interface; the goals — (A) each $a_n(f)$ an algebraic integer,
  (B) $K_f=\mathbb{Q}(a_n)$ a number field, and the LMFDB label canonicity — are all **proved from
  (FIH)** (machine-checked, axiom-clean).
- **IHR-a (Manin module).** $\mathbb{M} = \big(\operatorname{Div}^0(\mathbb{P}^1(\mathbb{Q}))
  \otimes_{\mathbb{Z}}\operatorname{Sym}^{k-2}(\mathbb{Z}^2)\big)_{\Gamma_1(N)}$ is a finitely
  generated $\mathbb{Z}$-module — **proved** (Manin telescoping; $\Gamma_1(N)$ finitely generated;
  finitely many cusps). We use the homology side $\mathbb{M}$ with the period map
  $\iota:S_k\to\operatorname{Hom}_{\mathbb{Z}}(\mathbb{M},\mathbb{C})$, equivalent to your
  $S_k\hookrightarrow H_{\mathbb{Z}}\otimes\mathbb{C}$.
- **IHR-b (integral Hecke action).** The integral $T_n$ (with $U_p$ at $p\mid N$) and diamond actions
  on $\mathbb{M}$, the symbol-side commutativity, and the **Hecke/diamond-equivariance** of $\iota$ —
  all **proved**.
- **Abstract endgame.** "$\iota$ injective $+$ equivariant $+$ symbol operators commute $+$
  $\mathbb{M}$ finite $\Rightarrow$ (FIH)" — **proved**.
- **Group-cohomology realization (your cited route).** Following your pointer to Eichler–Shimura via
  group cohomology, we built the divisor $1$-cocycle $u(a)=(a\cdot c_0)-(c_0)$ as a genuine element of
  **Mathlib's** $Z^1(\Gamma_1(N),\operatorname{Div}^0)$, with the inverse relation
  $\rho(a)u(a^{-1})=-u(a)$ — **proved**. (Mathlib has recently acquired low-degree group cohomology.)
- **$k=1$** is isolated as a separate input per your "out of scope, Deligne–Serre" — see §3.

So, exactly per your plan, **everything is done except IHR-c/IHR-d** — the analytic period pairing and
the **injectivity** of $\iota$. An axiom audit confirms the entire downstream chain (the integrality
of $a_n$, $K_f$ a number field, the labels) depends, beyond Mathlib's standard axioms, *only* on this
one remaining input (for $k\ge2$) and on the $k=1$ lattice input (§3).

---

## 1. The decision your reply deferred — now forced

Your integration note recorded one open decision: *"whether to fully formalise IHR-c/IHR-d (the
analytic period pairing + injectivity) vs. isolate (IHR)/(FIH) as a cited classical input."* We have
now driven IHR-d as far as it goes, and the decision is forced.

We reduced **injectivity of $\iota$ (IHR-d)** — via positive-definiteness of the Petersson product and
a proved Green-type identity — to a **single analytic identity (IHR-c)**, Shimura's (8.2.22). With
$A(f,g):=(f,g)+(-1)^{k-2}(g,f)$:
$$\textbf{(IHR-c)}\qquad A(f,g)\;=\;\sum_i c_i(g)\,\big\langle\text{period of }f\text{ against }y_i\big\rangle,
\quad y_i\in\operatorname{Div}^0\otimes\operatorname{Sym}^{k-2}\ (\text{boundary symbols}).$$
Given (IHR-c): all periods of $f$ vanish $\Rightarrow A(f,\cdot)=0$; take $g=i^{k-2}f$ to get
$A(f,i^{k-2}f)=2\,i^{k-2}(f,f)$ (proved), so $(f,f)=0$, so $f=0$. That is the whole of injectivity.

**We have proved most of the machinery surrounding (IHR-c)** (all axiom-clean): $A(f,g)$ as a
symmetrized Petersson area integral over a $\Gamma_1(N)$-fundamental domain; the binomial expansion of
the integrand $f\,\overline{g}\,y^{k-2}$ into a finite sum of holomorphic $\times$ antiholomorphic
period-form products; a **curvilinear single-tile region-Stokes theorem** on the standard
$\mathrm{SL}_2(\mathbb{Z})$ tile (the genuinely hard Green's-theorem step, built on Mathlib's
divergence theorem after a Type-I/II split and arc reparametrization); the FTC edge-period assembly;
and a concrete **nonzero** $\Gamma_1(N)$-paired Manin boundary (side-pairing element
$\left(\begin{smallmatrix}1&0\\N&1\end{smallmatrix}\right)$) into which the edge periods telescope.

**What remains is the assembly of (IHR-c) across the fundamental-domain tiling**, and we now believe
that step is a multi-month modular-curve-boundary build (the precise obstruction is §2). Hence the
forced decision:

> **(i)** commit to fully formalizing (IHR-c) — the area-to-boundary-period identity over the tiling;
> or **(ii)** isolate (FIH) — or (IHR-c) itself — as a **cited classical input** (it is Shimura
> Thm 3.51 / Diamond–Shurman Ch. 6, entirely standard), keeping everything downstream rigorous modulo
> that single citation.

We would value your view on whether (ii) is acceptable mathematical practice here, or whether the
project's goals warrant (i). And — the heart of this brief — whether there is a **third option**: a
route to injectivity that sidesteps (IHR-c) entirely (§2).

---

## 2. Why the tiling assembly is hard, and the precise new question

**The obstruction (empirically established).** The fundamental domain is realized as a finite tiling
by $\mathrm{SL}_2(\mathbb{Z})$-translates of the standard tile. Using the single-tile Stokes theorem
forces a per-tile change of variables, which **slashes the cusp forms differently on each tile**, so
the integrands on a shared interior edge differ and the interior edges do **not** cancel. The natural
fix — integrate the single $\Gamma_1(N)$-invariant form *without* slashing, so a global primitive
cancels interior edges for free — we implemented and tested: it **moves** the obstruction rather than
removing it. Our single-tile Stokes theorem is specific to the standard tile's **Type-I region**
(bounded by the unit-circle arc); a Möbius-translated tile is not Type-I, so Mathlib's divergence
theorem does not apply to it, and there is no region-Stokes for a translated / non-convex curvilinear
union. After any arrangement of cancellation, the residue is the **Manin↔Siegel model change** —
identifying which tile edges constitute the outer cusp-geodesic Manin boundary — which is exactly the
modular-symbol boundary geometry with no Mathlib foothold. (We also verified that the $S$/$T$
side-pairing *relocates* content into nonzero tail periods rather than annihilating it, so there is no
elementary cancellation shortcut.)

**The precise new question: is there a route to injectivity (IHR-d) that avoids (IHR-c)?**

- **(a) Group-cohomology cup product.** You cited Eichler–Shimura via group cohomology
  (arXiv:1701.00611), and we now have the divisor cocycle inside Mathlib's $H^1$. Can injectivity of
  $\iota$ be obtained from the **non-degeneracy of the cup product / Petersson pairing on**
  $H^1_{\mathrm{par}}(\Gamma_1(N),\operatorname{Sym}^{k-2})$, **without** the geometric
  fundamental-domain boundary integral (8.2.22)? Concretely: is there a cohomological proof that a
  cusp form whose period class in $H^1_{\mathrm{par}}$ vanishes must be zero — one that needs only the
  single integration-by-parts already encoded in our single-tile Stokes theorem, not the global
  tiling assembly?
- **(b) A $q$-expansion route to injectivity.** Can "all periods of $f$ vanish $\Rightarrow f=0$" be
  proved directly from the Fourier expansion — e.g. expressing enough periods (or period polynomials)
  as explicit linear functionals of the $a_n(f)$ and inverting — thereby bypassing the Petersson
  product and the boundary identity altogether?
- **(c) Has the cost calculus shifted?** Your reply judged the $q$-expansion lattice "stronger than
  necessary" *relative to the period route*, and flagged two real defects in it (per-character
  coefficients involve $\chi(d)$, forcing an $\mathcal{O}_{\mathbb{Q}(\chi)}$-lattice not a
  $\mathbb{Z}$-one; a $\mathbb{Z}[1/N]$-model misses bad-prime integrality). But the period route's
  injectivity is now proving to be the multi-month boundary build above. Weighing that against those
  two defects: do you still see the modular-symbol/period route as the lighter path to (FIH), or has
  one of (a), (b), or the lattice become preferable?

---

## 3. $k = 1$

Per your guidance ($k=1$ out of scope, $\operatorname{Sym}^{-1}$ makes the cohomological construction
break, Deligne–Serre territory), we have left $k<2$ on a separate input: the existence of a full-rank,
Hecke-stable, finite free $\mathbb{Z}$-lattice $\Lambda\subset S_k(\Gamma_1(N))$ (which, via a proved
"faithful action on a full-rank lattice $\Rightarrow$ (FIH)" lemma valid for *all* weights, would also
re-prove $k\ge2$). Since $\dim_{\mathbb{C}}S_k(\Gamma_1(N))<\infty$ is already in hand in our
development, the finiteness and freeness of $\Lambda$ are routine; the only deep content is **full
rank** ($\Lambda\otimes\mathbb{C}=S_k$, the rationality / $q$-expansion principle). Two questions:

- Is isolating $k=1$ as this lattice input (cited to Deligne–Serre) the right disposition, or would you
  restrict the headline results to $k\ge2$ and treat $k=1$ as genuinely separate downstream?
- Does the integral-$q$-expansion-lattice argument go through at $k=1$ *without* the full
  Deligne–Serre apparatus, given that we already have finite-dimensionality and the (integer-times-root-of-unity)
  Hecke coefficient formula?

---

## 4. Soundness / faithfulness check

We would like a sanity check that the two isolated inputs are faithfully stated, with no hidden
strengthening or vacuity (this is a recurring concern in formalization, where a too-strong or
vacuously-satisfiable hypothesis can silently trivialize a result):

- **(IHR-c)** pairs $A(f,g)$ against a **concrete nonzero** Manin boundary cycle (the
  $(1-g_0)\cdot\{0,\infty\}$ symbol for the side-pairing $g_0=\left(\begin{smallmatrix}1&0\\N&1\end{smallmatrix}\right)$),
  so the identity is *not* vacuously satisfied by a zero right-hand side; and we have a witness that
  the left-hand side equals the genuine (nonzero) symmetrized area integral.
- The **lattice input** states full rank explicitly and *derives* faithfulness of the Hecke action
  from it (rather than assuming faithfulness).

Do these match the content you would expect of Shimura (8.2.22) and Thm 3.52 respectively, or have we
mis-stated either?

---

## 5. Definitions and notation (reference)

Conventions as in the previous brief. Briefly: $S_k(\Gamma_1(N))$ = weight-$k$ cusp forms;
$q=e^{2\pi i z}$; $n:=k-2$; Hecke $T_n$ (with $U_p$ at $p\mid N$) and diamonds $\langle d\rangle$;
$\mathbb{T}_{\mathbb{Z}}=\mathbb{Z}[T_n,\langle d\rangle]\subseteq\operatorname{End}_{\mathbb{C}}(S_k)$;
Petersson product $(f,g)$ (Hermitian, positive-definite); newform = normalized ($a_1=1$) new
eigenform; $K_f=\mathbb{Q}(a_n)$, $\mathcal{O}_f=\operatorname{image}(\lambda_f:\mathbb{T}_{\mathbb{Z}}
\to\mathbb{C})$. $\mathbb{M}=(\operatorname{Div}^0(\mathbb{P}^1\mathbb{Q})\otimes\operatorname{Sym}^{k-2}
\mathbb{Z}^2)_{\Gamma_1(N)}$; period map $\iota(f)(\{\alpha\to\beta\}\otimes P)=\int_\alpha^\beta
f(z)P(z,1)\,dz$.

## 6. References

- **[Shimura 1971]** *Introduction to the Arithmetic Theory of Automorphic Functions*: §3.5
  ((3.5.20); Thm 3.48(3), integrality; Thm 3.51(1), $[K_f:\mathbb{Q}]\le\dim_{\mathbb{C}}S_k$;
  Thm 3.52, integral $q$-expansion basis); §8.2 (the period theory; (8.2.17)–(8.2.22); (8.2.18c)).
- **[Diamond–Shurman 2005]** *A First Course in Modular Forms*: §5.4 (Manin symbols, side-pairings,
  boundary map); Thm 5.8.2(a) (newform is a full eigenform); Ch. 6, Thm 6.5.1 (integral structure).
- **[Miyake 2006]** *Modular Forms*: Thm 4.5.9, Thm 4.5.19(2).
- **[Manin 1972]** "Parabolic points and zeta functions of modular curves."
- **Eichler–Shimura via group cohomology** (arXiv:1701.00611) — your prior citation; central to §2(a).
- **[Deligne–Serre 1974]** "Formes modulaires de poids 1" — §3.

## 7. Document metadata

- Project: Hecke-eigenvalue arithmetic of newforms ("Group A"), AINTLIB Lean monorepo; Mathlib v4.31.0-rc2.
- Generated: 2026-06-24; follow-up to the 2026-06-19 brief + reply.
- Build status: the whole development compiles; the *only* non-foundational dependencies are
  (IHR-c) (for $k\ge2$) and the $k=1$ lattice input. The headline results (integrality of $a_n$; $K_f$
  a number field; label canonicity) are proved modulo exactly these.
- Length: ~2,600 words.
