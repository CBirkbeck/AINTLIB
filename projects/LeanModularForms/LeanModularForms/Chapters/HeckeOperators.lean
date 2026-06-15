import Verso
import VersoManual
import VersoBlueprint
import LeanModularForms.HeckeRIngs.GL2.HeckeAction
import LeanModularForms.HeckeRIngs.GL2.HeckeModularForm
import LeanModularForms.HeckeRIngs.GL2.HeckeModularForm_Gamma0
import LeanModularForms.HeckeRIngs.GL2.HeckeT_n
import LeanModularForms.HeckeRIngs.GL2.FourierHecke
import LeanModularForms.HeckeRIngs.GL2.Unified.RingTransport

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Hecke operators on modular forms" =>

The abstract $`\mathrm{GL}_2` Hecke algebra acts on spaces of modular forms. A double coset acts
on a function $`\mathbb{H}\to\mathbb{C}` through the weight-$`k` slash action summed over a set of
left-coset representatives, and this action preserves both modularity and cuspidality. Assembling
these operators over all double cosets yields ring homomorphisms $`\mathbb{T}\to\operatorname{End}(M_k)`
from the Hecke algebra into the endomorphisms of weight-$`k` forms, both at level one and for
$`\Gamma_0(N)`. Specialising to the congruence setting produces the classical diamond operators
$`\langle n\rangle` and the Hecke operators $`T(n)` on forms of level $`\Gamma_1(N)`, which satisfy
the usual multiplicativity and recurrence laws together with the classical formulas for their
Fourier coefficients \[DS, Ch. 5\].

:::definition "heckeSlash" (lean := "HeckeRing.GL2.heckeSlash")
*Hecke slash action.*
Fix a weight $`k\in\mathbb{Z}` and a double coset class $`D` of the arithmetic $`\mathrm{GL}_2`
Hecke pair, with representative $`\delta`. Write the right-coset decomposition of the double coset
as $`SL_2(\mathbb{Z})\,\delta\,SL_2(\mathbb{Z})=\bigsqcup_i (\sigma_i\delta)\,SL_2(\mathbb{Z})`,
indexed by representatives $`\sigma_i\in SL_2(\mathbb{Z})`. The *Hecke slash action* of $`D` sends a
function $`f\colon\mathbb{H}\to\mathbb{C}` to
$$`
  f\,|_k\,D \;=\; \sum_i f\,\big|_k\,(\sigma_i\delta)^{\mathsf{T}},
`
the sum over those representatives of the weight-$`k` slash action of the transposed matrices. Each
$`(\sigma_i\delta)^{\mathsf{T}}=\delta^{\mathsf{T}}\sigma_i^{\mathsf{T}}` is a left-coset
representative, since transposition is an anti-involution that fixes $`SL_2(\mathbb{Z})` and the
double coset, so the right-coset decomposition above transposes to a left-coset decomposition
$`SL_2(\mathbb{Z})\,\delta\,SL_2(\mathbb{Z})=\bigsqcup_i SL_2(\mathbb{Z})\,(\delta^{\mathsf{T}}\sigma_i^{\mathsf{T}})`.

For a single matrix $`\alpha\in\mathrm{GL}_2(\mathbb{Q})` of positive determinant, the weight-$`k`
slash action used here is the normalised action
$$`
  (f\,|_k\,\alpha)(\tau) \;=\; \det(\alpha)^{\,k-1}\, j(\alpha,\tau)^{-k}\, f(\alpha\cdot\tau),
`
where $`\alpha\cdot\tau` is the action on the upper half-plane by Möbius transformation, the factor
$`j(\alpha,\tau)` is the automorphy factor $`c\tau+d` of the bottom row $`(c,d)` of $`\alpha`, and the
determinant is normalised by the weight $`\det(\alpha)^{\,k-1}`. The representatives $`\sigma_i\delta`
all have positive determinant, so this is exactly the factor appearing in each summand. The resulting
function $`f\,|_k\,D` is independent of the chosen representatives, distributes over addition of
functions, commutes with scalar multiplication, and sends the zero function to zero.

Depends on: {uses "hecke-coset"}[] {uses "GL-pair"}[]
:::

:::definition "heckeOperator" (lean := "HeckeRing.GL2.heckeOperator, HeckeRing.GL2.heckeOperatorLinear")
*Hecke operator on modular forms.*
Fix a weight $`k\in\mathbb{Z}` and a double coset class $`D` of the level-one $`\mathrm{GL}_2` Hecke
pair. The Hecke slash action $`f\mapsto f|_k D` carries a modular form $`f` of weight $`k` for
$`SL_2(\mathbb{Z})` to another such modular form: the resulting function on $`\mathbb{H}` is again
*slash-invariant* under $`SL_2(\mathbb{Z})` and remains *holomorphic and bounded at the cusp*. These
two facts — slash-invariance of the summed action and boundedness at the cusp — are exactly what
upgrade the bare slash action to a genuine modular form, so the construction defines a map
$$`
  T(D)\colon M_k(SL_2(\mathbb{Z})) \longrightarrow M_k(SL_2(\mathbb{Z})),\qquad T(D)f = f|_k D.
`
Because the slash action distributes over addition of functions and commutes with scalar
multiplication, this map is additive and homogeneous, and hence a $`\mathbb{C}`-linear endomorphism
of the space $`M_k(SL_2(\mathbb{Z}))` of weight-$`k` modular forms for $`SL_2(\mathbb{Z})`.

Depends on: {uses "heckeSlash"}[]
:::

:::definition "heckeRingHom" (lean := "HeckeRing.GL2.heckeRingHom")
*The Hecke algebra acting on modular forms.*
Fix a weight $`k\in\mathbb{Z}`. Assembling the individual Hecke operators over all double cosets of
the level-one $`\mathrm{GL}_2` Hecke pair gives a single *ring homomorphism*
$$`
  \mathbb{T} \longrightarrow \operatorname{End}_{\mathbb{C}}\!\bigl(M_k(\mathrm{SL}_2(\mathbb{Z}))\bigr)
`
from the abstract $`\mathrm{GL}_2` Hecke algebra $`\mathbb{T}` into the $`\mathbb{C}`-linear
endomorphisms of the space $`M_k(\mathrm{SL}_2(\mathbb{Z}))` of weight-$`k` modular forms for
$`\mathrm{SL}_2(\mathbb{Z})`. On a single double coset $`D` it is the assignment $`D\mapsto(f\mapsto
f\,|_k\,D)`, and it is extended to an arbitrary element by additivity: a formal $`\mathbb{Z}`-linear
combination $`T=\sum_D c_D\,[D]` is sent to the endomorphism $`\sum_D c_D\,T(D)`. This is automatically
additive and respects the zero element and the identity double coset.

That this assignment is also *multiplicative* — and hence a genuine ring homomorphism — is the
substantive point. On double cosets it rests on the compatibility of the slash action with
composition: composing the operators of two double cosets reproduces the Hecke slash action of their
product in $`\mathbb{T}`, that is $`T(D_1)\circ T(D_2)=T(D_2\cdot D_1)` as maps on forms. Combined with
the commutativity of the Hecke algebra $`\mathbb{T}`, this upgrades to multiplicativity on all of
$`\mathbb{T}`, so the construction respects products and is a ring homomorphism (Shimura, Proposition
3.30).

Depends on: {uses "heckeOperator"}[] {uses "hecke-ring"}[]
:::

:::definition "heckeRingHom-Gamma0" (lean := "HeckeRing.GL2.heckeRingHom_Gamma0")
*The congruence Hecke ring acting on level-$`\Gamma_0(N)` modular forms.*
Fix a positive integer $`N` and a weight $`k\in\mathbb{Z}`. The level-$`N` analogue of the
construction above attaches to each double coset of the congruence Hecke pair
$`(\Gamma_0(N),\Delta_0(N))` an endomorphism of the space $`M_k(\Gamma_0(N))` of weight-$`k`
modular forms for $`\Gamma_0(N)`. On a double coset $`D=\Gamma_0(N)\,\delta\,\Gamma_0(N)`, with left-coset
decomposition $`\bigsqcup_i \Gamma_0(N)\,\alpha_i`, a form $`f` is sent to the summed weight-$`k`
slash $`f\mapsto\sum_i f\mid_k\alpha_i`. This summed slash again transforms correctly under
$`\Gamma_0(N)` and stays holomorphic and bounded at every cusp, so it lands back in
$`M_k(\Gamma_0(N))`, and it is additive and homogeneous, hence a $`\mathbb{C}`-linear endomorphism
$`T(D)\colon M_k(\Gamma_0(N))\to M_k(\Gamma_0(N))`. No Nebentypus twist is applied: the action is on
the full space of $`\Gamma_0(N)`-invariant forms.

Assembling these operators over all double cosets gives a single *ring homomorphism*
$$`
  R(\Gamma_0(N),\Delta_0(N)) \longrightarrow \operatorname{End}_{\mathbb{C}}\!\bigl(M_k(\Gamma_0(N))\bigr)
`
from the congruence Hecke ring $`R(\Gamma_0(N),\Delta_0(N))` with $`\mathbb{Z}` coefficients into the
$`\mathbb{C}`-linear endomorphisms of $`M_k(\Gamma_0(N))`. A formal $`\mathbb{Z}`-linear combination
$`T=\sum_D c_D\,[D]` is sent to $`\sum_D c_D\,T(D)`, which is automatically additive and respects the
zero element and the identity double coset. *Multiplicativity* is again the substantive point: composing
the operators of two double cosets reproduces the slash action of their product in the ring, so that
$`T(D_1)\circ T(D_2)=T(D_2\cdot D_1)` on forms, and combined with the commutativity of
$`R(\Gamma_0(N),\Delta_0(N))` this upgrades to multiplicativity on the whole ring (Shimura, Proposition
3.30, at level $`\Gamma_0(N)`).

Depends on: {uses "heckeOperator"}[] {uses "gamma0-pair"}[]
:::

:::definition "diamondOp" (lean := "HeckeRing.GL2.diamondOp_n")
*Diamond operator on level-$`\Gamma_1(N)` forms.*
Fix a positive integer $`N`, a weight $`k\in\mathbb{Z}`, and a positive integer $`n`. The *diamond
operator* $`\langle n\rangle` is an endomorphism of the space $`M_k(\Gamma_1(N))` of weight-$`k`
modular forms for $`\Gamma_1(N)`, defined by cases according to whether $`n` is coprime to the level.

When $`\gcd(n,N)=1`, the residue of $`n` modulo $`N` is a unit of $`\mathbb{Z}/N\mathbb{Z}`, and
$`\langle n\rangle` acts by the weight-$`k` slash action of any matrix $`\gamma\in\Gamma_0(N)` whose
lower-right entry is congruent to $`n` modulo $`N`,
$$`
  \langle n\rangle f \;=\; f\,\big|_k\,\gamma,\qquad
  \gamma=\begin{pmatrix} a & b\\ c & d\end{pmatrix}\in\Gamma_0(N),\quad d\equiv n \pmod N.
`
Such a $`\gamma` always exists, and the result is *independent of the chosen representative*: any two
matrices of $`\Gamma_0(N)` with the same lower-right entry modulo $`N` differ by an element of the
normal subgroup $`\Gamma_1(N)`, under which $`f` is invariant, so the slashed forms agree. Because
$`\Gamma_1(N)` is normal in $`\Gamma_0(N)`, this slash again lands in $`M_k(\Gamma_1(N))`, and it is
additive and homogeneous, hence a $`\mathbb{C}`-linear endomorphism. The value $`\langle n\rangle`
depends only on the residue class of $`n` modulo $`N`; in particular $`\langle 1\rangle` is the
identity and the assignment is multiplicative in the unit, $`\langle m\rangle\langle n\rangle=\langle
mn\rangle` for $`m,n` coprime to $`N`.

When $`\gcd(n,N)>1`, no such matrix exists and the operator is set to the *zero endomorphism*,
$`\langle n\rangle=0`. This convention is what makes $`\langle n\rangle` vanish at indices dividing
the level, matching the recurrence governing the Hecke operators $`T_{p^r}` at primes $`p\mid N`.

Depends on: {uses "heckeSlash"}[]
:::

:::definition "heckeT-n" (lean := "HeckeRing.GL2.heckeT_n")
*The Hecke operator $`T(n)` for general $`n`.*
Fix a positive integer $`N`, a weight $`k\in\mathbb{Z}`, and a positive integer $`n`. The Hecke
operator $`T(n)` is a $`\mathbb{C}`-linear endomorphism of the space $`M_k(\Gamma_1(N))` of weight-$`k`
modular forms for $`\Gamma_1(N)`, assembled multiplicatively from prime-power components along the
factorisation of $`n`.

The building block at a single prime $`p` is the operator $`T(p)`. When $`p` is coprime to $`N` it is
the level-$`N` Hecke operator attached to the double coset of $`\operatorname{diag}(1,p)`, given
explicitly on a form $`f` by the summed weight-$`k` slash over coset representatives
$$`
  T(p)f \;=\; \sum_{b=0}^{p-1} f\,\big|_k\,\begin{pmatrix}1 & b\\ 0 & p\end{pmatrix}
    \;+\; \bigl(\langle p\rangle f\bigr)\,\big|_k\,\begin{pmatrix}p & 0\\ 0 & 1\end{pmatrix},
`
where $`\langle p\rangle` is the diamond operator (Diamond–Shurman, Proposition 5.2.1). When instead
$`p\mid N`, only the upper-triangular sum survives,
$$`
  T(p)f \;=\; \sum_{b=0}^{p-1} f\,\big|_k\,\begin{pmatrix}1 & b\\ 0 & p\end{pmatrix},
`
in accordance with the convention $`\langle p\rangle = 0` for $`p\mid N`. Both expressions land back in
$`M_k(\Gamma_1(N))`, so $`T(p)` is a well-defined linear endomorphism.

The prime-power operators $`T(p^v)` are then defined by the three-term recurrence
$$`
  T(p^{0}) = \mathrm{id},\qquad T(p^{1}) = T(p),\qquad
  T(p^{v+2}) \;=\; T(p)\,T(p^{v+1}) \;-\; p^{\,k-1}\,\langle p\rangle\,T(p^{v}),
`
where the products are composition of endomorphisms and the scalar $`p^{\,k-1}` is the
weight-$`k` normalisation of the diamond term (Diamond–Shurman (5.10), Shimura Theorem 3.24(6)). When
$`p\mid N` the diamond term vanishes and the recurrence collapses to $`T(p^{v}) = T(p)^{v}`.

Finally, writing the prime factorisation $`n=\prod_p p^{\,v_p(n)}` with $`v_p(n)` the multiplicity of
$`p` in $`n`, the operator $`T(n)` is the composition of the corresponding prime-power components,
$$`
  T(n) \;=\; \prod_{p \mid n} T\bigl(p^{\,v_p(n)}\bigr),
`
constructed recursively by peeling off the smallest prime factor of $`n` together with its full
multiplicity. For $`n=1` the empty product gives $`T(1) = \mathrm{id}`. Because the prime-power
components for distinct primes commute, this product is independent of the order of the factors.

Depends on: {uses "diamondOp"}[] {uses "heckeSlash"}[]
:::

:::theorem "heckeT-n-mult" (lean := "HeckeRing.GL2.heckeT_n_mul_coprime, HeckeRing.GL2.heckeT_ppow_succ_succ")
*Classical multiplicative structure of the Hecke operators $`T(n)`.*
Fix an integer weight $`k` and a level $`N \geq 1`, and consider the family of Hecke operators
$`T(n)`, for $`n \geq 1`, acting on the space of weight-$`k` modular forms for $`\Gamma_1(N)`. They
satisfy the two classical relations that, together, determine every $`T(n)` from the operators at
prime arguments.

*Coprime multiplicativity.* For any two strictly positive integers $`m` and $`n` that are coprime
to each other and to the level $`N`,
$$`
  T(mn) \;=\; T(m)\,T(n).
`

*Prime-power recurrence.* For a prime $`p`, the operators on the successive powers $`p^{v}` are tied
together by the three-term relation
$$`
  T(p^{\,v+2}) \;=\; T(p)\,T(p^{\,v+1}) \;-\; p^{\,k-1}\,\langle p\rangle\,T(p^{\,v}),
`
valid for every exponent $`v \geq 0`, with base cases $`T(p^{0}) = \mathrm{id}` and $`T(p^{1}) =
T(p)`. Here $`\langle p\rangle` is the diamond operator at $`p`, extended so that it vanishes when
$`p` divides $`N`; in that case the diamond term drops out and the recurrence collapses to
$`T(p^{\,v}) = T(p)^{\,v}`. The scalar $`p^{\,k-1}` is the weight-normalised determinant factor
carried by the level-raising operator. No coprimality of $`p` to $`N` is required for the recurrence:
it holds uniformly, the coprime and dividing cases being unified through the extended diamond
operator. Together these two laws reduce the whole family $`\{T(n)\}_{n \geq 1}` to the prime-power
operators, and those in turn to the operators $`T(p)` at primes.

Depends on: {uses "heckeT-n"}[] {uses "diamondOp"}[]
:::

:::proof "heckeT-n-mult"
*Coprime multiplicativity* is **transported from the Hecke ring**. Inside the commutative ring
$`R(\Gamma_0(N), \Delta_0(N))` ({bpref "commring-Gamma0"}[]) the ring-side elements $`D_n` —
assembled by the same prime-power recurrence and `minFac`-peeling as the operators — satisfy
$`D_{mn} = D_m D_n` for coprime $`m, n` by pure commutative algebra ({bpref "gamma0-mult-table"}[]
records the full multiplication table). The character-space homomorphisms send $`D_n` to
$`\chi(n)^{-1}\,T(n)` on each Nebentypus subspace $`M_k(N,\chi)` ({uses "charSpace-bridge"}[]),
so applying them to the ring identity yields $`T(mn) = T(m)\,T(n)` on every $`M_k(N,\chi)`; the
character decomposition $`M_k(\Gamma_1(N)) = \bigoplus_\chi M_k(N,\chi)`
({uses "charSpace-directSum"}[]) then glues the identity to the whole space. No operator-level
coset combinatorics enters.

*Prime-power recurrence.* This is the defining relation of $`T(p^{\,v})`: the operators on prime
powers are introduced precisely by the three-term recursion above, with the two base values
$`T(p^{0}) = \mathrm{id}` and $`T(p^{1}) = T(p)`, so the displayed identity holds by construction for
every $`v`. The extended diamond operator is defined to be zero when $`p` divides $`N`, which makes
the recurrence valid without any coprimality hypothesis and degenerates it to $`T(p^{\,v}) =
T(p)^{\,v}` in the ramified case.

Depends on: {uses "heckeT-n"}[] {uses "diamondOp"}[]
:::

:::theorem "heckeT-n-comm" (lean := "HeckeRing.GL2.heckeT_n_comm, HeckeRing.GL2.heckeT_n_comm_diamondOp")
*The Hecke operators commute, and commute with the diamond operators.*
Fix a level $`N \geq 1` and an integer weight $`k`, and consider the family of Hecke operators
$`T(n)`, for $`n \geq 1`, together with the diamond operators $`\langle d\rangle` indexed by residue
classes $`d` modulo $`N`, all acting on the space $`M_k(\Gamma_1(N))` of weight-$`k` modular forms
for $`\Gamma_1(N)`.

*Pairwise commutativity of the Hecke operators.* For any two strictly positive integers $`m` and
$`n` coprime to the level $`N` (no coprimality between $`m` and $`n` themselves is required), the
corresponding operators commute,
$$`
  T(m)\,T(n) \;=\; T(n)\,T(m).
`

*Commutation with the diamond operators.* For every $`n \geq 1` coprime to $`N` and every residue
class $`d` modulo $`N`, the Hecke operator $`T(n)` commutes with the diamond operator
$`\langle d\rangle`,
$$`
  \langle d\rangle\,T(n) \;=\; T(n)\,\langle d\rangle.
`
Thus the operators $`\{T(n)\}_{n \geq 1}` and $`\{\langle d\rangle\}_{d}` form a single commuting
family, the standing hypothesis behind the simultaneous diagonalisation of the Hecke algebra
\[DS, Proposition 5.2.4\].

Depends on: {uses "heckeT-n"}[] {uses "heckeT-n-mult"}[] {uses "diamondOp"}[]
:::

:::proof "heckeT-n-comm"
*Commutativity is inherited from the ring.* The Hecke ring $`R(\Gamma_0(N), \Delta_0(N))` is
commutative — Shimura's anti-involution argument applied to the Atkin–Lehner-conjugated transpose
({bpref "commring-Gamma0"}[]). For indices coprime to $`N` the character-space homomorphisms
identify the restriction of $`T(n)` to each Nebentypus subspace $`M_k(N,\chi)` with the scalar
multiple $`\chi(n)` of the image of the ring element $`D_n` ({uses "charSpace-bridge"}[]).
Commutativity of the ring therefore forces the restricted operators to commute on every
$`M_k(N,\chi)`, and the character decomposition ({uses "charSpace-directSum"}[]) glues these
identities to all of $`M_k(\Gamma_1(N))`. The former self-contained coset-combinatorial induction
has been retired in favour of this transport.

*Commutation with the diamond operators* needs no ring input at all: on each Nebentypus subspace
the diamond operator acts as the scalar $`\chi(d)` (and the operators $`T(n)` preserve each
subspace, by a direct block induction over their construction), so the two visibly commute
summand-by-summand, and the direct sum decomposition again glues the conclusion.

Depends on: {uses "heckeT-n"}[] {uses "heckeT-n-mult"}[] {uses "diamondOp"}[]
:::

:::theorem "fourierCoeff-heckeT-n" (lean := "HeckeRing.GL2.fourierCoeff_heckeT_n_period_one")
*Fourier coefficients of $`T(n)` on a Nebentypus space (Diamond–Shurman, Proposition 5.3.5).*
Fix a positive level $`N`, a weight $`k\in\mathbb{Z}`, and a Dirichlet-type character
$`\chi\colon(\mathbb{Z}/N\mathbb{Z})^{\times}\to\mathbb{C}^{\times}`. Let $`f` be a weight-$`k`
modular form for $`\Gamma_1(N)` that lies in the $`\chi`-isotypic (Nebentypus) subspace, so that the
diamond operator acts by $`\langle d\rangle f=\chi(d)\,f` for every $`d` coprime to $`N`. Write its
Fourier expansion at the canonical period $`1` as $`f=\sum_{m\ge 0} a_m\,q^m` with $`q=e^{2\pi i\tau}`,
and let $`n` be a positive integer coprime to $`N`. Then for every $`m\ge 0` the $`m`-th Fourier
coefficient of $`T(n)f` is the twisted divisor sum
$$`
  a_m\bigl(T(n) f\bigr) \;=\; \sum_{\substack{d \,\mid\, \gcd(m,n) \\ \gcd(d,N)=1}}
    d^{\,k-1}\,\chi(d)\, a_{mn/d^2},
`
the sum running over the positive divisors $`d` of $`\gcd(m,n)`, where a divisor sharing a factor with
$`N` contributes nothing (its diamond term $`\langle d\rangle` vanishes). Equivalently, with the
diamond operator left in place, $`a_m\bigl(T(n) f\bigr)=\sum_{d\mid\gcd(m,n)} d^{\,k-1}\,
a_{mn/d^2}\bigl(\langle d\rangle f\bigr)`. All Fourier coefficients are taken at the canonical period
$`1`, at which $`a_m` is the standard $`m`-th coefficient of a $`\Gamma_1(N)`-form.
:::

:::proof "fourierCoeff-heckeT-n"
The operator $`T(n)` is built multiplicatively from its prime-power components: writing the prime
factorisation of $`n`, one has $`T(n)=\prod_{p}T(p^{v_p})`, and these prime-power operators commute,
so the formula need only be established prime by prime and then propagated by the multiplicativity of
both sides. The base case is the single prime $`p`, where unfolding the Hecke slash action over an
explicit set of left-coset representatives — the upper-triangular matrices $`\begin{pmatrix}a&b\\
0&d\end{pmatrix}` with $`ad=p` and $`0\le b<d` — expresses $`T(p)f` as a finite sum of slashed
translates of $`f`. Each translate contributes a geometric sum $`\sum_{b} e^{2\pi i\,bm/d}` over the
offsets $`b`, and this sum is $`d` when $`d\mid m` and $`0` otherwise, by orthogonality of the additive
characters $`e^{2\pi i\,(\cdot)}`. Collecting the surviving terms yields the prime recurrence: the
coefficient of $`T(p)f` at $`m` is a combination of $`a_{pm}` and the diamond-twisted $`a_{m/p}`, the
factor $`d^{\,k-1}=p^{\,k-1}` coming from the determinant normalisation of the weight-$`k` slash and
the twist $`\chi(p)` from the action of $`\langle p\rangle` on the $`\chi`-isotypic space.

From the prime case the prime-power formula follows by induction on the exponent, using the
three-term recurrence $`T(p^{v+1})=T(p)\,T(p^{v})-p^{\,k-1}\langle p\rangle\,T(p^{v-1})`, which on
Fourier coefficients reproduces exactly the divisor sum over the powers of $`p` dividing $`\gcd(m,p^{v})`;
when $`p\mid N` the diamond term $`\langle p\rangle` is zero and the recurrence degenerates to
$`T(p)^{v}`. Finally, for general $`n` one combines the prime-power formulas across distinct primes: a
divisor of $`\gcd(m,n)` factors uniquely into prime-power divisors, the multiplicativity of
$`d\mapsto d^{\,k-1}\chi(d)` matches the product of the per-prime weights, and the iterated index
$`mn/d^2` is assembled from the per-prime quotients. This reduction of the divisor sum over a composite
modulus to the convolution of the prime-power sums delivers the stated formula, with the coprimality
hypothesis $`\gcd(n,N)=1` ensuring every diamond twist appearing is a genuine character value.

Depends on: {uses "heckeT-n"}[] {uses "diamondOp"}[]
:::

:::definition "hecke-eigenvalue" (lean := "HeckeRing.GL2.eigenvalue, HeckeRing.GL2.eigenvalue_eq_fourierCoeff_one")
*Hecke eigenvalue of a common eigenform.*
Fix a positive integer $`N` and a weight $`k\in\mathbb{Z}`. Call a modular form $`f` of weight $`k`
for $`\Gamma_1(N)` a *common eigenform* if it is a simultaneous eigenfunction of all the Hecke
operators $`T(n)` with $`n` coprime to $`N`: for every such $`n` there is a scalar
$`\lambda\in\mathbb{C}` with
$$`
  T(n)\,f \;=\; \lambda\,f .
`
Given such an $`f`, its *eigenvalue at $`n`*, written $`\lambda_n(f)`, is the scalar so determined,
extracted as a choice witnessing the eigenfunction condition; it is characterised by the eigenvalue
equation $`T(n)\,f = \lambda_n(f)\,f`. Since $`f` is nonzero, this scalar is in fact unique, but the
definition only records that it satisfies the eigenvalue equation.

Now suppose in addition that $`f` lies in the character (Nebentypus) eigenspace
$`M_k(\Gamma_1(N),\chi)` for a Dirichlet character $`\chi` modulo $`N`, and that $`f` is *normalised*,
meaning its first Fourier coefficient is $`a_1(f) = 1`. Then for every $`n` coprime to $`N` the
eigenvalue coincides with the $`n`-th Fourier coefficient of $`f`,
$$`
  \lambda_n(f) \;=\; a_n(f) ,
`
where $`a_n(f)` denotes the $`n`-th coefficient of the $`q`-expansion of $`f` taken at the canonical
period $`1` (Miyake, Theorem 4.5.16). Concretely, applying the divisor-sum Fourier formula for
$`T(n)` to the first coefficient collapses the divisor sum to its single term $`d = 1`, which together
with the normalisation $`a_1(f) = 1` yields $`a_1\bigl(T(n)f\bigr) = a_n(f)`; comparing with the
eigenvalue equation $`a_1\bigl(T(n)f\bigr) = \lambda_n(f)\,a_1(f) = \lambda_n(f)` gives the identity.

Depends on: {uses "heckeT-n"}[] {uses "fourierCoeff-heckeT-n"}[]
:::
