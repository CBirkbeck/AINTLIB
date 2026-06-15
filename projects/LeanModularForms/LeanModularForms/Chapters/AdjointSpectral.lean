import Verso
import VersoManual
import VersoBlueprint
import LeanModularForms.HeckeRIngs.GL2.AdjointTheory
import LeanModularForms.HeckeRIngs.GL2.AdjointTheoryPetersson

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Adjoints and the spectral theorem" =>

With respect to the Petersson inner product the Hecke operators on a space of cusp forms
have explicit adjoints. The starting point is a change-of-variables identity: for
$`\alpha \in \mathrm{GL}_2^{+}(\mathbb{Q})` the slashes satisfy
$`\langle f|_k\alpha,\ g\rangle = \langle f,\ g|_k\alpha'\rangle`, where
$`\alpha' = \det(\alpha)\,\alpha^{-1}` is the adjugate of $`\alpha` \[DS, Prop. 5.5.2\]. Applied
to the double cosets defining $`T(n)`, this yields $`T(n)^{*} = \langle n\rangle^{-1}\,T(n)`
whenever $`n` is coprime to the level $`N` \[DS, Thm. 5.5.3\]; in particular each such $`T(n)`
commutes with its adjoint, so it is a *normal* operator. The spectral theorem for a commuting
family of normal operators on the finite-dimensional inner product space of cusp forms then
produces an orthogonal basis of simultaneous eigenforms for all the $`T(n)` with $`(n,N)=1`
\[DS, Thm. 5.5.4\]. This chapter records the change-of-variables identity that drives the entire
argument.

:::theorem "petersson-slash-adjoint" (lean := "HeckeRing.GL2.peterssonInner_slash_adjoint")
*The change-of-variables adjoint identity.*
Fix an integer weight $`k`. Let $`\alpha` be an invertible real $`2\times 2` matrix with
positive determinant, $`\det(\alpha) > 0`, and let $`\alpha'` denote its adjugate, so that
$`\alpha\,\alpha' = \det(\alpha)\,I` and hence $`\alpha' = \det(\alpha)\,\alpha^{-1}`. Then for
any measurable region $`D \subseteq \mathcal{H}` of the upper half-plane and any functions
$`f, g : \mathcal{H} \to \mathbb{C}`,
$$`
  \langle f|_k\alpha,\ g\rangle_{D}
    \;=\;
  \langle f,\ g|_k\alpha'\rangle_{\alpha\,D},
`
where $`\langle\,\cdot\,,\,\cdot\,\rangle_{D}` is the weight-$`k` Petersson pairing obtained by
integrating $`\overline{f(\tau)}\,g(\tau)\,(\operatorname{Im}\tau)^{k}` against the hyperbolic
measure over $`D`, the region $`\alpha\,D` is the image of $`D` under the Möbius action of
$`\alpha`, and $`|_k` is the weight-$`k` slash operator. Taking $`D` to be a fundamental domain
and $`\alpha \in \mathrm{GL}_2^{+}(\mathbb{Q})` normalising the relevant congruence subgroup
recovers Diamond–Shurman's Proposition 5.5.2 for cusp forms.

Depends on: {uses "petN"}[]
:::

:::proof "petersson-slash-adjoint"
The identity is a change of variables $`\tau \mapsto \alpha\,\tau` in the Petersson integral.
Writing $`g = (g|_k\alpha^{-1})|_k\alpha`, the cocycle property of the slash operator lets one
peel an $`\alpha` off both arguments of the integrand simultaneously: the weight-$`k` factors of
automorphy attached to $`\alpha` acting on $`\overline{f}` and on $`g` recombine, and since
$`\det(\alpha) > 0` the determinant twist contributes a single scalar $`|\det(\alpha)|^{k-2}`.
Concretely, the integrand $`\overline{(f|_k\alpha)(\tau)}\,g(\tau)\,(\operatorname{Im}\tau)^{k}`
equals $`|\det(\alpha)|^{k-2}` times the value at $`\alpha\,\tau` of the integrand for the pair
$`f` and $`g|_k\alpha^{-1}`.

It remains to absorb this scalar into the right-hand argument. Slashing $`g` by the adjugate
$`\alpha'` produces exactly the factor $`|\det(\alpha)|^{k-2}` over the action of $`\alpha^{-1}`,
because $`\alpha'` and $`\alpha^{-1}` induce the same Möbius transformation of the upper
half-plane and differ only by the determinant scaling; thus $`g|_k\alpha'` carries the same
twist that the change of variables generated. Finally, for $`\det(\alpha) > 0` the Möbius action
of $`\alpha` preserves the hyperbolic measure, so integrating the transported integrand over the
image region $`\alpha\,D` equals integrating the original over $`D`. Combining these three steps
gives the stated equality of pairings.
:::

:::theorem "heckeT-p-adjoint" (lean := "HeckeRing.GL2.heckeT_p_adjoint")
*Diamond–Shurman Theorem 5.5.3 at a prime: the Petersson adjoint of $`T_p`.*
Fix an integer weight $`k` and a level $`N \geq 1`, and let $`p` be a prime that is coprime to
$`N`. Write $`\langle\,\cdot\,,\,\cdot\,\rangle_N` for the level-$`N` Petersson inner product on
the space of cusp forms of weight $`k` for $`\Gamma_1(N)`, let $`T_p` denote the $`p`-th Hecke
operator on this space, and let $`\langle p\rangle` denote the diamond operator attached to the
residue class of $`p` modulo $`N`. Then for all cusp forms $`f` and $`g` of weight $`k` for
$`\Gamma_1(N)`,
$$`
  \langle T_p\, f,\ g\rangle_N
    \;=\;
  \langle f,\ \langle p\rangle^{-1}\, T_p\, g\rangle_N .
`
Equivalently, the adjoint of $`T_p` with respect to $`\langle\,\cdot\,,\,\cdot\,\rangle_N` is the
operator $`\langle p\rangle^{-1}\, T_p`; since the diamond operator is unitary and commutes with
$`T_p`, this exhibits each such $`T_p` as a normal operator.

Depends on: {uses "petersson-slash-adjoint"}[] {uses "petN"}[] {uses "diamondOp"}[]
:::

:::proof "heckeT-p-adjoint"
The Hecke operator $`T_p` is given by a sum over a fixed set of coset representatives of the
double coset defining it, each representative acting on a cusp form through the weight-$`k` slash.
Inserting this decomposition into the left-hand pairing turns $`\langle T_p\, f,\ g\rangle_N` into
a finite sum of Petersson pairings $`\langle f|_k\alpha_i,\ g\rangle_N`, one for each
representative $`\alpha_i`. Applying the change-of-variables adjoint identity to every summand
moves the slash off the first argument and onto the second: $`\langle f|_k\alpha_i,\ g\rangle_N`
becomes $`\langle f,\ g|_k\alpha_i'\rangle_N`, where $`\alpha_i'` is the adjugate of
$`\alpha_i`. Because $`p` is coprime to $`N`, the action of $`g` is invariant under the relevant
congruence subgroup, so the regions of integration realign and the level-$`N` pairing is
preserved throughout this transport.

It remains to identify the resulting sum of adjugate slashes on the right-hand argument. The
adjugate representatives $`\alpha_i'` do not lie in the original double coset, but they differ
from a genuine system of representatives only by an element normalising $`\Gamma_1(N)` whose
effect on cusp forms is precisely the diamond operator at $`p`. Collecting the adjugate slashes
and reindexing them back into the coset decomposition of $`T_p` therefore produces $`T_p\, g`
twisted by the inverse diamond operator, that is $`\langle p\rangle^{-1}\, T_p\, g`. Substituting
this into the right-hand pairing yields the claimed identity
$`\langle T_p\, f,\ g\rangle_N = \langle f,\ \langle p\rangle^{-1}\, T_p\, g\rangle_N`.
:::

:::theorem "heckeT-n-adjoint" (lean := "HeckeRing.GL2.heckeT_n_adjoint")
*Diamond–Shurman Theorem 5.5.3 in full: the Petersson adjoint of $`T_n`.*
Fix an integer weight $`k` and a level $`N \geq 1`. Let $`n \geq 1` be an integer coprime to
$`N`, write $`\langle\,\cdot\,,\,\cdot\,\rangle_N` for the level-$`N` Petersson inner product on the
space of cusp forms of weight $`k` for $`\Gamma_1(N)`, let $`T_n` denote the $`n`-th Hecke operator
on this space, and let $`\langle n\rangle` denote the diamond operator attached to the residue
class of $`n` modulo $`N`. Then for all cusp forms $`f` and $`g` of weight $`k` for $`\Gamma_1(N)`,
$$`
  \langle T_n\, f,\ g\rangle_N
    \;=\;
  \langle f,\ \langle n\rangle^{-1}\, T_n\, g\rangle_N .
`
Equivalently, the adjoint of $`T_n` with respect to $`\langle\,\cdot\,,\,\cdot\,\rangle_N` is the
operator $`\langle n\rangle^{-1}\, T_n`. This generalises the prime case to every index coprime to
the level; since the diamond operator is unitary and commutes with $`T_n`, it exhibits each such
$`T_n` as a normal operator, the input to the simultaneous diagonalisation of the Hecke algebra.

Depends on: {uses "heckeT-p-adjoint"}[] {uses "heckeT-n"}[] {uses "diamondOp"}[]
:::

:::proof "heckeT-n-adjoint"
The proof reduces the general index $`n` to the prime case by strong induction on $`n`, exploiting
the multiplicative structure of the Hecke operators. When $`n = 1` the operator is the identity and
the diamond twist is trivial, so the identity is immediate. For $`n > 1`, factor off the largest
prime power $`p^{v}` dividing $`n`, say $`n = p^{v}\,(n / p^{v})` with the two factors coprime.
Because the Hecke operators at coprime indices multiply, $`T_n = T_{p^{v}}\, T_{n / p^{v}}`, and the
diamond operator is multiplicative in the index; applying the inductive hypothesis to each smaller
factor and using that the diamond operators commute with all the $`T_m` recombines the two adjoint
identities into the one for $`n`. This splits the problem into the prime-power indices.

For a prime power $`p^{v}` (with $`p` coprime to $`N`) the argument is again inductive, this time on
the exponent. The base exponent $`v = 1` is exactly the prime case
$`\langle T_p f, g\rangle_N = \langle f, \langle p\rangle^{-1} T_p g\rangle_N`. For $`v \geq 2` the
Hecke relation
$$`
  T_{p^{v}} \;=\; T_p\, T_{p^{v-1}} \;-\; p^{\,k-1}\,\langle p\rangle\, T_{p^{v-2}}
`
expresses $`T_{p^{v}}` through lower powers. Distributing the Petersson pairing across this
three-term recurrence and feeding in the prime case together with the inductive hypotheses for
$`T_{p^{v-1}}` and $`T_{p^{v-2}}` moves all three slashes onto the second argument; the diamond
twists accumulated along the way multiply to $`\langle p^{v}\rangle^{-1} = \langle p\rangle^{-v}`,
and reassembling the same recurrence on the right reproduces $`\langle p^{v}\rangle^{-1} T_{p^{v}} g`.
Conjugating the scalar $`p^{\,k-1}`, which is real, leaves it fixed, so no extra factor survives.
This closes the prime-power case, and with the multiplicative step it closes the general claim.
:::

:::theorem "heckeT-n-normal" (lean := "HeckeRing.GL2.heckeT_n_normal")
*Diamond–Shurman Theorem 5.5.4 input: each $`T_n` is a normal operator.*
Fix an integer weight $`k` and a level $`N \geq 1`, and let $`n \geq 1` be an integer coprime to
$`N`. Write $`\langle\,\cdot\,,\,\cdot\,\rangle_N` for the level-$`N` Petersson inner product on the
space of cusp forms of weight $`k` for $`\Gamma_1(N)`, let $`T_n` denote the $`n`-th Hecke operator
on this space, and let $`\langle n\rangle` denote the diamond operator attached to the residue class
of $`n` modulo $`N`. By the adjoint identity the Petersson adjoint of $`T_n` is
$`T_n^{*} = \langle n\rangle^{-1}\, T_n`, and $`T_n` commutes with it: as operators on cusp forms of
weight $`k` for $`\Gamma_1(N)`,
$$`
  T_n\,\bigl(\langle n\rangle^{-1}\, T_n\bigr)
    \;=\;
  \bigl(\langle n\rangle^{-1}\, T_n\bigr)\, T_n .
`
Thus $`T_n\, T_n^{*} = T_n^{*}\, T_n`, exhibiting each such $`T_n` as a *normal* operator with
respect to $`\langle\,\cdot\,,\,\cdot\,\rangle_N`. Normality is exactly the hypothesis required by
the spectral theorem, so it is the entry point for the simultaneous diagonalisation of the family of
Hecke operators of index coprime to the level.

Depends on: {uses "heckeT-n-adjoint"}[] {uses "heckeT-n-comm"}[]
:::

:::proof "heckeT-n-normal"
By the adjoint identity the Petersson adjoint of $`T_n` is the twisted operator
$`\langle n\rangle^{-1}\, T_n`, so checking normality amounts to verifying that $`T_n` commutes with
$`\langle n\rangle^{-1}\, T_n`. Both factors of this adjoint already live in the commutative Hecke
action: the diamond operator $`\langle n\rangle^{-1}` commutes with every Hecke operator, and $`T_n`
trivially commutes with itself. Consequently $`T_n` may be moved past the diamond twist and past the
second copy of $`T_n`, giving
$`T_n\,\bigl(\langle n\rangle^{-1}\, T_n\bigr) = \langle n\rangle^{-1}\, T_n\, T_n
= \bigl(\langle n\rangle^{-1}\, T_n\bigr)\, T_n`. Hence $`T_n` commutes with its adjoint and is
normal.
:::

:::theorem "simultaneous-eigenform-basis" (lean := "HeckeRing.GL2.exists_simultaneous_eigenform_basis")
*Diamond–Shurman Theorem 5.5.4: an orthogonal basis of simultaneous Hecke eigenforms.*
Fix an integer weight $`k`, a level $`N \geq 1`, and a Dirichlet character
$`\chi \colon (\mathbb{Z}/N\mathbb{Z})^{\times} \to \mathbb{C}^{\times}` modulo $`N`. Consider the
Nebentypus space $`S_k(N,\chi)` of cusp forms of weight $`k` for $`\Gamma_1(N)` on which the
diamond operators act through $`\chi`, equipped with the level-$`N` Petersson inner product
$`\langle\,\cdot\,,\,\cdot\,\rangle_N`, and assume this space is finite-dimensional over
$`\mathbb{C}`. Then there is a *finite* subset $`B \subseteq S_k(N,\chi)` of cusp forms with the
following three properties:

* every element of $`B` lies in the character space $`S_k(N,\chi)`;
* every element of $`B` is a *simultaneous eigenform* for the whole family of Hecke operators
  $`T_n` with $`(n,N)=1`, meaning that for each such index $`n` there is a scalar
  $`\lambda_n \in \mathbb{C}` with $`T_n\,f = \lambda_n\,f`;
* the elements of $`B` are pairwise *orthogonal* for the Petersson inner product: if $`f, g \in B`
  and $`f \neq g` then $`\langle f,\ g\rangle_N = 0`.

In particular $`B` is an orthogonal basis of $`S_k(N,\chi)` consisting of common eigenforms of
every $`T_n` coprime to the level. This is the simultaneous diagonalisation of the commutative
Hecke algebra, the culmination of the adjoint theory of this chapter.

Depends on: {uses "heckeT-n-normal"}[] {uses "petN-definite"}[] {uses "heckeT-n"}[] {uses "petN"}[]
:::

:::proof "simultaneous-eigenform-basis"
The finitely many operators $`T_n` with $`(n,N)=1` form a *commuting family of normal operators*
on the finite-dimensional space $`S_k(N,\chi)`. Normality is the content of the preceding result,
and commutativity holds because all Hecke operators of index coprime to the level commute with one
another. Equipping $`S_k(N,\chi)` with the Petersson inner product makes it a genuine
inner-product space — positive-definiteness is exactly the statement that the Petersson norm of a
nonzero cusp form is nonzero — so the spectral theorem for a commuting family of normal operators
applies. It decomposes the space as an internal orthogonal direct sum of the *joint
eigenspaces*: for each tuple of eigenvalues $`(\lambda_n)_{(n,N)=1}` one forms the simultaneous
eigenspace $`\bigcap_{(n,N)=1}\ker(T_n - \lambda_n)`, and these subspaces span $`S_k(N,\chi)`,
are mutually independent, and — because two simultaneous eigenforms with different eigenvalue
tuples differ at some single $`T_n` whose adjoint is the unitarily twisted $`T_n` — are pairwise
Petersson-orthogonal.

It remains to extract the basis. Within each joint eigenspace choose an orthonormal basis with
respect to the inner product induced from the Petersson pairing; every vector so chosen is
automatically a common eigenform of all the $`T_n`, since it lies in the corresponding
simultaneous eigenspace. Collecting these bases across the finitely many joint eigenspaces yields a
single basis of the whole space, and because the eigenspaces are mutually orthogonal the collected
family remains orthonormal — in particular pairwise orthogonal. Taking $`B` to be the (finite) set
of these basis vectors furnishes the asserted orthogonal basis of simultaneous Hecke eigenforms.
:::
