# Follow-up questions — T-W7 group law (round 2, revised 2026-07-07)

*Thank you — the reply was decisive. Since then we have acquired the primary sources (Mumford GIT,
Mumford's Abelian Varieties, Bosma–Lenstra 1995, Lange–Ruppert 1985), and this changes the picture:
the rigidity question we were going to ask is now resolved by transcription from GIT itself. What
remains is one scope question and two confirmations.*

**Status update on rigidity (what was F1).** GIT Prop. 6.1's proof supplies exactly the
globalization mechanism the earlier sketch left open, and it is *not* a density argument: for the
case where $X/S$ has a section and $p$ is closed, one forms the largest closed subscheme $Z \subseteq
X$ where $f = \eta \circ p$; the one-point case (a ringed-space argument using $p_*\mathcal O_X =
\mathcal O_S$ over an Artinian base) applied to **every Artinian subscheme** $T \subset S$
concentrated at $t$ shows $Z \supseteq p^{-1}(T)$ scheme-theoretically, whence (Krull intersection,
coherence, $p$ closed) $Z$ contains $p^{-1}(U_0)$ for an open $U_0 \ni t$; then $U_1 = \{t :
p^{-1}(t) \subseteq Z\} = S \setminus p(X - Z)$ is clopen ($p$ flat hence open), so connectedness of
$S$ finishes. The corollary chain 6.2 → 6.3 → 6.4 → 6.6 gives uniqueness of the group law verbatim.
Our elliptic curve has a section, so the sectionless case (fppf descent) is never needed. We will
formalise this as stated — with one consequence, hence:

> **F1′ (noetherian scope).** GIT Ch. 6 works over **locally noetherian** schemes, and the proof
> genuinely uses this (Artinian subschemes concentrated at a point; Krull intersection in noetherian
> local rings; coherence of the ideal of $Z$). So the canonicity we can formalise now is: *over a
> locally noetherian base, a locally-Weierstrass elliptic curve has exactly one group-scheme
> structure with the given identity.* Extending to arbitrary $S$ requires the EGA IV §8 spreading-out
> technique (Faltings–Chai Rem. 1.2(a) names exactly this), i.e. descent of the finitely presented
> data $(E, e, m, m')$ to a finitely generated $\mathbb Z$-subalgebra — infrastructure our library
> does not yet have. **Question: is locally-noetherian canonicity sufficient for every downstream
> use in the moduli programme** (representability of $Y(N)$/$Y_1(N)$, comparison with the abstract
> genus-one definition, deformation-theoretic arguments — all of which seem to live over bases
> locally of finite type over $\mathbb Z$ or over Artinian rings)? Or do you foresee a genuine use
> of canonicity over a non-noetherian base, which would justify prioritising the spreading-out
> machinery?

> **F2 (Bosma–Lenstra instantiation — confirmation).** We now have the paper. We plan to use the two
> addition laws corresponding (via their Theorem 2 bijection with $\mathbb P^2$) to the lines
> $Z = 0$ and $Y = 0$: the first is exceptional exactly on the diagonal ($P_1 - P_2 = O$), the
> second exactly where $P_1 - P_2 \in E \cap \{Y = 0\}$, and the two loci are disjoint over every
> field since $O \notin \{Y=0\}$. Coefficients enter the §5 formulas polynomially, so the same
> formulas define the law over any ring, each valid on an open of $E \times E$ (their §1 remark).
> Our covering argument over an arbitrary base: the two exceptional loci are closed, their
> complements are open, and disjointness of the exceptional loci **fibrewise over all fields**
> implies the two opens cover $E \times_S E$ topologically. Do you agree this instantiation and the
> fibrewise-to-global covering step are sound, and do you know of any subtlety in the $\{Y=0\}$-law
> in characteristics 2, 3 (the paper's genericity assumptions all appear characteristic-free, but a
> second pair of eyes is welcome)?

> **F3 (comparison theorem — unchanged from the previous draft).** For the gluing over a general
> base we need: *any isomorphism of projective Weierstrass models over a ring $R$ carrying the point
> at infinity to the point at infinity is induced by a unique coordinate change $(u,r,s,t) \in
> R^\times \times R^3$.* Without it, two local Weierstrass presentations of the same $(E,e)$ on an
> overlap need not be related by a coordinate change, and the per-chart group laws' agreement would
> circularly require canonicity. Our intended proof, uniform over every ring: a pointed isomorphism
> preserves the affine part $E \setminus O$; the induced ring isomorphism preserves the pole-order
> filtration $F_n$ (defined via the ideal sheaf of the section); freeness $F_2 = R \oplus Rx$,
> $F_3 = R \oplus Rx \oplus Ry$ forces $x' \mapsto \alpha x + \beta$, $y' \mapsto \gamma y + \delta
> x + \epsilon$ with $\alpha, \gamma$ units; matching the two Weierstrass relations forces
> $\alpha^3 = \gamma^2$, and $u := \gamma/\alpha$ gives the coordinate change. (a) Do you agree the
> comparison theorem is genuinely required at this point? (b) Is the filtration argument the
> standard proof over an arbitrary base (Katz–Mazur §2.2-style), and are there pitfalls over rings
> with nilpotents or many idempotents? (c) Is uniqueness of $(u,r,s,t)$ automatic from the
> filtration argument, or does it need a separate small argument?

---

**Note on the Γ₁(N) remark in your last message.** We checked the claim against the current
formalisation before acting on it, and it appears to describe a stale draft: the definition of
record is Katz–Mazur 1.4.1 exactly — the degree-$N$ divisor $[P] + [2P] + \dots + [NP]$ required to
be a *subgroup divisor* (Deligne's exact-order condition), with **no** equality against the
degree-$N^2$ divisor $E[N]$ anywhere in the $\Gamma_1$ layer; the equality with $E[N]$ is used only
for full level-$N$ structures $(P,Q)$ via $\sum_{a,b}[aP+bQ] = E[N]$, as it should be. The current
programme brief also states this distinction explicitly (twice, with the $N$ vs $N^2$ degree
warning). So no fix is needed there — but do say if you had a *different* location in mind.

**Also note:** questions F1′, F2, F3 above were not addressed in your last message — we would still
very much value answers to those three.
