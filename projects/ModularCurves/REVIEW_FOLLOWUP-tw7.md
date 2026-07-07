# Follow-up questions — T-W7 group law (round 2, 2026-07-07)

*Thank you — the reply was decisive: we have adopted the uniform per-ring computation of
$\Gamma(\mathrm{ProjModel}(W),\mathcal O) \cong R$ (retiring cohomology-and-base-change entirely),
the open-cover-and-glue construction of $m_U$, the global equivariance upgrade, the bundled atlas,
and the existence/canonicity milestone split. In auditing the reply against our formal requirements,
three points need one more round.*

---

**F1 (the rigidity globalization step — this is the critical one).** Your sketch establishes, for
$h : A \times_S A \to B$ vanishing on both axes ($h|_{A\times e} = h|_{e\times A} = e$):

1. *(affine core)* $\mathrm{Hom}_S(X \times_S Y, Z_{\mathrm{aff}}) \cong \mathrm{Hom}_S(Y,
   Z_{\mathrm{aff}})$ from universal $\pi_*\mathcal O = \mathcal O$ — clean, we can formalise this;
2. *(local step)* the properness/closed-image argument produces an **open** $Y' \subseteq A$
   containing the zero section with $h|_{A \times_S Y'} = e$.

But the passage from the open neighbourhood $A \times_S Y'$ to **all of** $A \times_S A$ is exactly
what your own Q6 answer rules out over a non-reduced base: agreement on an open set (even a
topologically dense one, even one containing the section) does not propagate past nilpotents, and
the corollary derivation ("rigidity first makes it factor through one projection, then the second
restriction forces the factor to be zero") appears to use a **global** factorisation that step 2
does not deliver. We tried and failed to close this ourselves (translation by $T$-points;
scheme-density of the neighbourhood; associated-point/support arguments), and we will not invent the
step. Could you give the **exact statement of GIT Prop. 6.1** (verbatim if possible) and the precise
mechanism by which the factorisation becomes global over an arbitrary — possibly non-reduced,
possibly non-noetherian — base? In particular: does the connectedness/propagation argument run along
$Y$, along $S$, or fibrewise; is a noetherian reduction (EGA IV §8) part of the intended proof; or
is there an infinitesimal/Artinian argument that handles the nilpotent directions? A
formalisation-friendly complete proof of just the corollary we need (two group laws with common
identity coincide) would be equally welcome.

**F2 (confirming the concrete cover for $m_U$).** For your open-cover-and-glue recommendation we
propose to instantiate the cover with the **Bosma–Lenstra complete system of two addition laws of
bidegree $(2,2)$** (Bosma–Lenstra, *J. Number Theory* 53 (1995) 229–240; building on
Lange–Ruppert): two explicit polynomial triples for the long Weierstrass cubic whose exceptional
divisors are disjoint over every field, so their regularity opens cover $E \times E$ over any base,
and all overlap/on-curve checks become polynomial identities over $\mathbb Z[a_1,\dots,a_6]$ modulo
the curve relations. Three checks: (a) do you agree this is the right instantiation (rather than the
five ad-hoc secant/tangent/anti-diagonal/unit/infinity pieces)? (b) is the general — long, all
characteristics — Weierstrass case fully covered by the two-law system in Bosma–Lenstra as stated,
or only short forms? (c) any known pitfalls in using their laws over an arbitrary *ring* (the
identities being over $\mathbb Z[a_i]$, we expect none beyond size)?

**F3 (a dependency we believe the plan needs and the reply did not address).** For the gluing over a
general base we need the **comparison theorem**: *any isomorphism of projective Weierstrass models
over a ring $R$ carrying the point at infinity to the point at infinity is induced by a unique
coordinate change $(u,r,s,t) \in R^\times \times R^3$.* Without it, two local Weierstrass
presentations of the same $(E,e)$ on an overlap need not be related by a coordinate change, and the
per-chart group laws' agreement would circularly require canonicity. Our intended proof, uniform
over every ring: a pointed isomorphism preserves the affine part $E \setminus O$; the induced ring
isomorphism preserves the pole-order filtration $F_n$ (defined via the ideal sheaf of the section);
freeness $F_2 = R \oplus Rx$, $F_3 = R \oplus Rx \oplus Ry$ forces $x' \mapsto \alpha x + \beta$,
$y' \mapsto \gamma y + \delta x + \epsilon$ with $\alpha, \gamma$ units; matching the two Weierstrass
relations forces $\alpha^3 = \gamma^2$, and $u := \gamma/\alpha$ gives the coordinate change. (a) Do
you agree the comparison theorem is genuinely required at this point? (b) Is the filtration argument
the standard proof over an arbitrary base (Katz–Mazur §2.2-style), and are there pitfalls we should
expect over rings with nilpotents or many idempotents? (c) Is uniqueness of $(u,r,s,t)$ automatic
from the filtration argument, or does it need a separate small argument?
