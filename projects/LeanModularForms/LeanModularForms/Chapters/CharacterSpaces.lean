import Verso
import VersoManual
import VersoBlueprint
import LeanModularForms.HeckeRIngs.GL2.CharacterDecomp
import LeanModularForms.HeckeRIngs.GL2.Unified.NebentypusHeckeRingHom
import LeanModularForms.HeckeRIngs.GL2.Unified.RingTransport
import LeanModularForms.HeckeRIngs.GL2.Unified.ShimuraHom

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Character spaces and the diamond decomposition" =>

For each unit $`d` modulo $`N` the diamond operator $`\langle d\rangle` acts on the modular forms of level
$`\Gamma_1(N)` and weight $`k`, and these operators assemble into an action of the finite abelian group
$`(\mathbb{Z}/N\mathbb{Z})^\times` on the complex vector space $`M_k(\Gamma_1(N))`. Because the group is
finite abelian and $`\mathbb{C}` contains all roots of unity, this representation is simultaneously
diagonalisable, and the space splits as the direct sum, over the Dirichlet characters $`\chi` modulo $`N`,
of the Nebentypus eigenspaces $`M_k(N,\chi)`. Each summand is preserved by the congruence Hecke ring, so the
whole Hecke action respects the diamond decomposition and may be studied one character at a time. This is the
character-space decomposition of \[DS, §5.2\].

:::theorem "charSpace-directSum" (lean := "HeckeRing.GL2.ModularForm_Gamma1_charSpace_directSum")
*Diamond decomposition into Nebentypus spaces.*
Fix a positive integer $`N` and a weight $`k`. The diamond operators $`\langle d\rangle` for $`d` a unit
modulo $`N` give an action of the finite abelian group $`(\mathbb{Z}/N\mathbb{Z})^\times` on the space
$`M_k(\Gamma_1(N))` of modular forms of level $`\Gamma_1(N)` and weight $`k`. Indexing by the group of
Dirichlet characters $`\chi` modulo $`N`, the family of Nebentypus spaces $`M_k(N,\chi)` realises
$`M_k(\Gamma_1(N))` as their internal direct sum:
$$`
  M_k(\Gamma_1(N)) \;=\; \bigoplus_{\chi} M_k(N,\chi).
`
Equivalently, the spaces $`M_k(N,\chi)` are independent and together span $`M_k(\Gamma_1(N))`, so every
modular form of level $`\Gamma_1(N)` is uniquely a finite sum of forms carrying a single Nebentypus
character.

Depends on: {uses "modFormCharSpace"}[]
:::

:::proof "charSpace-directSum"
The diamond operators define a homomorphism from the finite abelian group $`(\mathbb{Z}/N\mathbb{Z})^\times`
into the endomorphisms of $`M_k(\Gamma_1(N))`, so each $`\langle d\rangle` has finite order. Over
$`\mathbb{C}` a finite-order operator is diagonalisable, and operators coming from a commutative group
commute with one another; hence the $`\langle d\rangle` form a commuting family of diagonalisable operators on
the finite-dimensional space $`M_k(\Gamma_1(N))`. Such a family can be simultaneously diagonalised: the space
is the direct sum of the joint eigenspaces, where on each summand every $`\langle d\rangle` acts as a single
scalar $`\lambda_d`. This already shows that the joint eigenspaces are independent and that their supremum is
the whole space.

It remains to identify the indexing. A nonzero joint eigenvector with eigenvalues $`\lambda_d` forces the
assignment $`d\mapsto\lambda_d` to be multiplicative and to send $`1` to $`1`, since the diamond operators
respect the group law; as each $`\lambda_d` is a root of unity, this assignment is exactly a Dirichlet
character $`\chi` modulo $`N`. Any system of eigenvalues that is not a character contributes only the zero
space, so the nontrivial joint eigenspaces are precisely the Nebentypus spaces $`M_k(N,\chi)`, one for each
Dirichlet character $`\chi` modulo $`N`. Reindexing the simultaneous diagonalisation over the character group
therefore exhibits $`M_k(\Gamma_1(N))` as the internal direct sum of the $`M_k(N,\chi)`.

Uses: {uses "modFormCharSpace"}[]
:::

:::theorem "charSpace-iSupIndep" (lean := "HeckeRing.GL2.CuspForm_Gamma1_iSupIndep_charSpace")
*Independence of the cusp-form Nebentypus spaces.*
Fix a positive integer $`N` and a weight $`k`, and let the diamond operators $`\langle d\rangle` for $`d`
a unit modulo $`N` act on the space $`S_k(\Gamma_1(N))` of cusp forms of level $`\Gamma_1(N)` and weight
$`k`. For each Dirichlet character $`\chi` modulo $`N` write $`S_k(N,\chi)` for the cusp forms on which
every $`\langle d\rangle` acts by the scalar $`\chi(d)`. Then the family of spaces $`S_k(N,\chi)`, indexed by
the characters $`\chi`, is *independent*: each $`S_k(N,\chi)` meets the span of all the others trivially,
$$`
  S_k(N,\chi) \;\cap\; \Bigl(\sum_{\psi \neq \chi} S_k(N,\psi)\Bigr) \;=\; 0.
`
Equivalently, a cusp form that is a sum of forms carrying single, pairwise-distinct Nebentypus characters
vanishes only when each summand does. This is the cusp-form counterpart of the diamond decomposition
{bpref "charSpace-directSum"}[]; together with the fact that the $`S_k(N,\chi)` span $`S_k(\Gamma_1(N))`,
it exhibits $`S_k(\Gamma_1(N))` as the internal direct sum of the $`S_k(N,\chi)`.

Depends on: {uses "modFormCharSpace"}[]
:::

:::proof "charSpace-iSupIndep"
The diamond operators on $`S_k(\Gamma_1(N))` form a commuting family: they are the images, under a single
monoid homomorphism from the abelian group $`(\mathbb{Z}/N\mathbb{Z})^\times`, of commuting group elements.
Each $`\langle d\rangle` has finite order, so over $`\mathbb{C}` it is diagonalisable, with the whole space
the sum of its eigenspaces. For a commuting family of diagonalisable operators on a finite-dimensional space
the joint eigenspaces are independent: a relation among nonzero vectors lying in joint eigenspaces with
distinct eigenvalue systems must be trivial, because two distinct eigenvalues of one operator have disjoint
eigenspaces. This is the operator-theoretic incarnation of the orthogonality of distinct characters.

Finally, distinct Dirichlet characters $`\chi \neq \psi` differ at some unit $`d`, so they assign different
scalars to $`\langle d\rangle` and hence pick out joint eigenspaces with distinct eigenvalue systems.
Restricting the independence of all joint eigenspaces along the injection of characters into eigenvalue
systems yields the independence of the cusp-form Nebentypus spaces $`S_k(N,\chi)`.

Uses: {uses "modFormCharSpace"}[]
:::

:::definition "heckeRingHomCharSpace" (lean := "HeckeRing.GL2.Unified.heckeRingHomCharSpace")
*The Hecke ring action on a Nebentypus space.*
Fix a positive integer $`N`, a weight $`k`, and a Dirichlet character $`\chi` modulo $`N`. The congruence
Hecke ring $`R(\Gamma_0(N),\Delta_0(N))` of the pair $`(\Gamma_0(N),\Delta_0(N))`, with $`\mathbb{Z}`
coefficients, acts on the Nebentypus space $`M_k(N,\chi)` by a ring homomorphism
$$`
  \Phi_\chi \colon R(\Gamma_0(N),\Delta_0(N)) \longrightarrow \operatorname{End}_{\mathbb{C}} M_k(N,\chi),
`
into the ring of $`\mathbb{C}`-linear endomorphisms of the eigenspace.

The action of a basis double coset $`\Gamma_0(N)\,\alpha\,\Gamma_0(N)` is the $`\chi`-twisted Hecke
operator: decomposing the double coset into finitely many left cosets $`\Gamma_0(N)\,\alpha_i`, a form $`f`
is sent to the weight-$`k` weighted sum of its slashes $`f\mid_k \alpha_i`, each summand twisted by the value
of $`\chi` on the relevant unit so that the result again carries the Nebentypus character $`\chi`. This
twisted slash preserves $`M_k(N,\chi)`, packages as a $`\mathbb{C}`-linear endomorphism, and extends
$`\mathbb{Z}`-linearly over the whole ring; the ring-homomorphism axioms are transported from the
corresponding identities for the operators acting on the underlying functions on the upper half-plane, using
that the coercion $`M_k(N,\chi)\hookrightarrow(\mathcal{H}\to\mathbb{C})` is injective.

On the standard generators at a good prime $`p\nmid N` the map is explicit: the prime double coset
$`\Gamma_0(N)\,\mathrm{diag}(1,p)\,\Gamma_0(N)` is sent to $`\chi(p)^{-1}` times the usual Hecke operator
$`T_p`, while the scalar double coset $`\Gamma_0(N)\,\mathrm{diag}(p,p)\,\Gamma_0(N)` is sent to the scalar
$`\chi(p)^{-1}\,p^{\,k-2}`. Because the source ring is commutative, all the resulting operators on
$`M_k(N,\chi)` commute.

Depends on: {uses "modFormCharSpace"}[] {uses "gamma0-pair"}[]
:::

:::theorem "charSpace-bridge" (lean := "HeckeRing.GL2.Unified.heckeRingHomCharSpace_heckeRingDn_all")
*The composite bridge: the ring action computes the Hecke operators.*
Fix a level $`N \ge 1`, a weight $`k`, and a Dirichlet character $`\chi` modulo $`N`.  For every
positive integer $`n` coprime to $`N`, the image of the ring element $`D_n` of
$`R(\Gamma_0(N),\Delta_0(N))` under the character-space homomorphism
({uses "heckeRingHomCharSpace"}[]) is the restriction to $`M_k(N,\chi)` of the classical Hecke
operator, rescaled by the character:
$$`
  \Phi_{\chi}(D_n) \;=\; \chi(n)^{-1}\,\bigl(T(n)\big|_{M_k(N,\chi)}\bigr).
`
Equivalently $`T(n)\big|_{M_k(N,\chi)} = \chi(n)\,\Phi_{\chi}(D_n)`: the construction of the
homomorphisms into the endomorphism rings *is* the construction of the Hecke operators on each
Nebentypus subspace, up to the explicit character scalar.  Together with the character
decomposition ({uses "charSpace-directSum"}[]) this transports every identity of the commutative
ring — commutativity, the multiplication table {bpref "gamma0-mult-table"}[] — to the operators
on all of $`M_k(\Gamma_1(N))`; see {bpref "heckeT-n-comm"}[] and {bpref "heckeT-n-mult"}[].

The coprimality restriction is essential and reflects an arithmetic fact, not a deficiency: the
twisted slash underlying $`\Phi_{\chi}` is built on the adjugate, which at a bad prime
$`p \mid N` exchanges the (then disjoint) double cosets of $`\operatorname{diag}(1,p)` and
$`\operatorname{diag}(p,1)` — so the ring image of $`D_p` at a bad prime is a $`V_p`-type
operator rather than $`U_p`.

Depends on: {uses "heckeRingHomCharSpace"}[] {uses "modFormCharSpace"}[] {uses "heckeT-n"}[]
:::

:::proof "charSpace-bridge"
Strong induction along the `minFac`-peeling of $`n`, all of whose prime factors are coprime to
$`N`.  Both sides decompose multiplicatively: the ring element peels as
$`D_n = D_{p^{v}}\,D_{n/p^{v}}` (coprime multiplicativity in the ring), the operator restriction
peels by its defining assembly, and the character scalar is multiplicative by construction.  The
prime-power case is itself an induction on the three-term recurrence, matching the recurrence
satisfied by $`\Phi_{\chi}(D_{p^{v}})` — under $`\Phi_{\chi}` the scalar class $`S_p` maps to
the explicit scalar $`\chi(p)^{-1} p^{\,k-2}`, which is exactly the diamond contribution
$`p^{\,k-1}\langle p\rangle` of the operator recurrence read on the $`\chi`-eigenspace.

Depends on: {uses "heckeRingHomCharSpace"}[] {uses "charSpace-directSum"}[]
:::

:::definition "fricke-operator" (lean := "HeckeRing.GL2.frickeOperator, HeckeRing.GL2.frickeCharEquiv")
*The Fricke involution.*
For a level $`N \ge 1` let $`W_N` be the matrix $`\begin{pmatrix}0 & -1\\ N & 0\end{pmatrix}`
(determinant $`N`).  Slashing by $`W_N` defines the *Fricke operator*
$`f \mapsto f|_k W_N` on $`M_k(\Gamma_1(N))`: the matrix $`W_N` normalises
$`\Gamma_1(N)` (and $`\Gamma_0(N)`), so the slash preserves modularity.  It conjugates the
diamond operators, $`W_N \circ \langle d\rangle = \langle d^{-1}\rangle \circ W_N`, hence
maps the Nebentypus subspace $`M_k(N,\chi)` to $`M_k(N,\bar{\chi})` (with
$`\bar{\chi} = \chi \circ (\cdot)^{-1}`), and its square is the explicit nonzero scalar
$`N^{2(k-1)}(-N)^{-k}`, so it packages as a linear equivalence
$`M_k(N,\chi) \simeq M_k(N,\bar{\chi})`.

Depends on: {uses "diamondOp"}[] {uses "modFormCharSpace"}[]
:::

:::definition "shimura-hom" (lean := "HeckeRing.GL2.Unified.heckeRingHomCharSpaceShimura")
*The Shimura-convention Hecke action `Ψ`.*
The character-space homomorphism $`\Phi_{\chi}` ({bpref "heckeRingHomCharSpace"}[]) is built
on the *adjugates* of the right-coset representatives; this makes it a homomorphism on the
nose, but at a bad prime $`p \mid N` it routes the class of
$`\operatorname{diag}(1,p)` to the disjoint adjugate class, so its image there is a
$`V_p`-type operator rather than $`U_p`.  The classical references (Shimura §3.5, Miyake
§4.5, Diamond–Shurman §5.2) instead sum over *left*-coset representatives — an
anti-homomorphism, absorbed by commutativity.  Because the project's Atkin–Lehner
anti-involution satisfies $`\iota(\delta) = W_N\,\operatorname{adj}(\delta)\,W_N^{-1}`,
that left-coset convention is realised with **no new coset theory** as the Fricke conjugate
$$`
  \Psi_{\chi}(T) \;=\; E^{-1} \circ \Phi_{\bar{\chi}}(T) \circ E,
`
where $`E` is the Fricke equivalence $`M_k(N,\chi) \simeq M_k(N,\bar{\chi})`
({uses "fricke-operator"}[]) — a ring homomorphism
$`R(\Gamma_0(N),\Delta_0(N)) \to \operatorname{End}_{\mathbb{C}} M_k(N,\chi)` by
construction.

Depends on: {uses "heckeRingHomCharSpace"}[] {uses "fricke-operator"}[] {uses "commring-Gamma0"}[]
:::

:::theorem "shimura-hom-Up" (lean := "HeckeRing.GL2.Unified.heckeRingHomCharSpaceShimura_D_p_bad")
*`Ψ` hits `U_p` at bad primes.*
For every prime $`p \mid N`, the Shimura-convention action sends the prime class to the
classical $`U_p` operator on each Nebentypus subspace:
$$`
  \Psi_{\chi}(D_p) \;=\; U_p\big|_{M_k(N,\chi)},
  \qquad U_p f \;=\; \sum_{b=0}^{p-1} f\big|_k \begin{pmatrix}1 & b\\ 0 & p\end{pmatrix},
`
with no character factor.  Together with the good-prime bridges for $`\Phi_{\chi}`
({bpref "charSpace-bridge"}[]) this realises the full classical picture: the Hecke ring of
the pair $`(\Gamma_0(N), \Delta_0(N))` acts on modular forms with the bad classes acting
as $`U_p` — as in Shimura and Miyake.

Depends on: {uses "shimura-hom"}[] {uses "gamma0-pair"}[]
:::

:::proof "shimura-hom-Up"
At a bad prime the right-coset representatives of
$`\Gamma_0(N)\operatorname{diag}(1,p)\Gamma_0(N)` are the $`p` lower-unipotent matrices
$`\delta_r = \begin{pmatrix}1 & 0\\ N r & p\end{pmatrix}`, $`r = 0,\dots,p-1`
(an index bijection with the abstract coset quotient, whose cardinality is the bad-class
degree $`p`; injectivity reduces to the fact that
$`\begin{pmatrix}1 & 0\\ N(r'-r)/p & 1\end{pmatrix}` lies in $`\Gamma_0(N)` only when
$`p \mid r' - r`).  Each $`\delta_r` has upper-left entry $`1`, so its Nebentypus weight
is $`1`, and the twisted slash sum collapses to
$`\sum_r g|_k \operatorname{adj}(\delta_r)` — the matching that is *true* for the
adjugate convention.  The Fricke conjugation then transforms each representative by the
machine-checked matrix identity
$`W_N\,\operatorname{adj}(\delta_r)\,W_N^{-1} = \begin{pmatrix}1 & r\\ 0 & p\end{pmatrix}`,
turning the adjugated sum into exactly the $`U_p` coset sum.

Depends on: {uses "shimura-hom"}[] {uses "fricke-operator"}[]
:::
