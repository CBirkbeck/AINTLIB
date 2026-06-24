import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import LeanModularForms.HeckeRIngs.GL2.Gamma1Pair
import LeanModularForms.HeckeRIngs.GL2.HeckeT_n
import LeanModularForms.HeckeRIngs.GL2.FourierHecke
import LeanModularForms.HeckeRIngs.GL2.CharacterDecomp
import LeanModularForms.HeckeRIngs.GL2.LevelRaise
import LeanModularForms.HeckeRIngs.GL2.AdjointTheory
import LeanModularForms.HeckeRIngs.GL2.AdjointTheoryPetersson
import LeanModularForms.HeckeRIngs.GL2.MultiplicationTable
import LeanModularForms.HeckeRIngs.GL2.Unified.RingTransport
import LeanModularForms.HeckeRIngs.GLn.TransposeAntiInvolution
import LeanModularForms.HeckeRIngs.GL2.Newforms.Basic
import LeanModularForms.HeckeRIngs.GL2.Newforms.CoeffSeq
import LeanModularForms.HeckeRIngs.GL2.Newforms.FullEigenform
import LeanModularForms.HeckeRIngs.GL2.Newforms.LevelRaiseComm
import LeanModularForms.HeckeRIngs.GL2.Newforms.MainLemma
import LeanModularForms.SMOObligations.StrongMultiplicityOneFull

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Strong Multiplicity One — Lean blueprint" =>

This is the blueprint for the [`LeanModularForms`](https://github.com/CBirkbeck/LeanModularForms)
formalisation of _strong multiplicity one_ for cusp forms (Miyake, _Modular Forms_,
Theorems 4.6.8 and 4.6.12): a newform is determined by all but finitely many of its
Hecke eigenvalues. The development is built on an abstract $`\mathrm{GL}_2` Hecke-ring
/ newform theory (`HeckeRing.GL2`), and the headline
$`\texttt{strongMultiplicityOne\_axiom\_clean}` is sorry-free and axiom-clean.

Each node carries a `(lean := …)` reference to the actual declaration in the
`LeanModularForms` library, so Verso reads its completion status directly from Lean, and
its prose cites the corresponding numbered result in Miyake (Chapter 4 — Hecke operators
in §4.5, newforms and strong multiplicity one in §4.6). The dependency graph at the foot
of the page records the logical spine.

# Hecke operators, diamond operators, and character spaces

:::definition "diamond-operator" (lean := "HeckeRing.GL2.diamondOpHom")
For a level $`N`, weight $`k`, and a unit $`d \in (\mathbb{Z}/N)^\times`, the _diamond
operator_ $`\langle d \rangle` acts on $`M_k(\Gamma_1(N))` by slashing with any
$`\gamma \in \Gamma_0(N)` whose lower-right entry reduces to $`d`. The diamonds form a
commuting family of finite-order (hence semisimple) operators, packaged as the monoid
homomorphism $`\texttt{diamondOpHom}`. Following Miyake §4.3.
:::

:::definition "hecke-character-space" (lean := "HeckeRing.GL2.modFormCharSpace")
Fix a level $`N` and weight $`k`. The space of modular forms decomposes under the
diamond operators $`\langle d \rangle` ({uses "diamond-operator"}[]) into _character
($`\chi`-isotypic) spaces_: for a Dirichlet character
$`\chi : (\mathbb{Z}/N)^\times \to \mathbb{C}^\times`,
$$`M_k(N, \chi) = \bigcap_{d} \ker\bigl(\langle d \rangle - \chi(d)\bigr),`
the intersection over all units $`d` of the $`\chi(d)`-eigenspaces of the diamonds, with
cusp-form analogue $`S_k(N, \chi)`. In `LeanModularForms` this is
$`\texttt{modFormCharSpace}`. Following Miyake §4.3.
:::

:::theorem "char-space-decomp" (lean := "HeckeRing.GL2.ModularForm_Gamma1_iSup_charSpace, HeckeRing.GL2.ModularForm_Gamma1_iSupIndep_charSpace")
The character spaces $`M_k(N, \chi)` are independent and span everything, giving the
_isotypic decomposition_ ({uses "hecke-character-space"}[])
$$`M_k(\Gamma_1(N)) = \bigoplus_{\chi} M_k(N, \chi),`
the sum over all characters $`\chi` of $`(\mathbb{Z}/N)^\times`. Following Miyake §4.3.
:::

:::proof "char-space-decomp"
Each diamond operator has finite order, hence is semisimple, and the diamonds pairwise
commute. A commuting family of semisimple operators is simultaneously diagonalisable, so
the whole space is the supremum of the joint eigenspaces (the character spaces), and
distinct joint eigenspaces are independent.
:::

:::definition "hecke-operator-tn" (lean := "HeckeRing.GL2.heckeT_n, HeckeRing.GL2.heckeT_n_cusp")
For $`n \ge 1` the _Hecke operator_ $`T_n` on $`M_k(\Gamma_1(N))` is assembled
multiplicatively from its prime-power components $`T_{p^r}`, with $`T_1 = \mathrm{id}`. It
restricts to cusp forms as $`\texttt{heckeT\_n\_cusp}`. Following Miyake §4.5
(Theorem 4.5.3).
:::

:::theorem "hecke-commute" (lean := "HeckeRing.GL2.heckeT_n_comm, HeckeRing.GL2.heckeT_n_mul_coprime")
For $`m, n` coprime to $`N` the Hecke operators commute, $`T_m T_n = T_n T_m`, and are
multiplicative on coprime indices, $`T_{mn} = T_m T_n` when $`\gcd(m, n) = 1`
({uses "hecke-operator-tn"}[]). Following Miyake Theorem 4.5.4.
:::

:::proof "hecke-commute"
Both identities are transported from the abstract $`\mathrm{GL}_2` Hecke ring
$`R(\Gamma_0(N), \Delta_0(N))`, which is commutative (it is the image of a polynomial
ring under the Satake-style presentation), via the ring homomorphism sending the
ring generator $`D_n` to $`T_n`.
:::

:::theorem "hecke-commute-diamond" (lean := "HeckeRing.GL2.heckeT_n_comm_diamondOp, HeckeRing.GL2.heckeT_n_preserves_charSpace")
The Hecke operators $`T_n` ($`\gcd(n,N)=1`) commute with the diamond operators
$`\langle d \rangle` ({uses "diamond-operator"}[], {uses "hecke-operator-tn"}[]); in
particular each $`T_n` preserves every character space $`M_k(N, \chi)`. Following Miyake
Theorem 4.5.4(2).
:::

:::proof "hecke-commute-diamond"
The diamond operators lie in the same commutative Hecke ring as the $`T_n`, so they
commute. Commuting with all $`\langle d \rangle` means $`T_n` preserves each joint
diamond eigenspace, i.e. each $`M_k(N, \chi)`.
:::

# Eigenforms and eigenvalue systems

:::definition "eigenform" (lean := "HeckeRing.GL2.Eigenform, HeckeRing.GL2.Eigenform.eigenvalue")
An _eigenform_ of level $`\Gamma_1(N)` and weight $`k` is a cusp form $`f` carrying a
Nebentypus character $`\chi` (so $`f \in S_k(N, \chi)`,
{uses "hecke-character-space"}[]) that is a simultaneous eigenvector of all Hecke
operators $`T_n` with $`\gcd(n, N) = 1` ({uses "hecke-operator-tn"}[]). Its _eigenvalue_
$`\lambda_n` is recorded by $`T_n f = \lambda_n f`. In `LeanModularForms` this is the
structure $`\texttt{Eigenform}` with $`\texttt{Eigenform.eigenvalue}`. Following Miyake
§4.5.
:::

:::theorem "eigenform-decomp" (lean := "HeckeRing.GL2.exists_eigenform_decomposition_mem_cuspFormsNew")
Any cusp form in the new subspace lying in a Nebentypus space $`S_k(N, \chi)` is a finite
sum of common Hecke eigenforms, each again new and of Nebentypus $`\chi`
({uses "eigenform"}[], {uses "cusp-forms-new-old"}[]). This is the simultaneous
diagonalisation underlying the whole theory.
:::

:::proof "eigenform-decomp"
The new subspace and the Nebentypus space are stable under every $`T_n`
({uses "hecke-commute-diamond"}[]). The $`\{T_n\}_{\gcd(n,N)=1}` form a commuting family
of diagonalisable operators on the finite-dimensional space $`S_k(N, \chi)`
({uses "hecke-commute"}[]), so the joint spectral decomposition restricts to the
invariant new subspace, exhibiting the form in a joint eigenbasis.
:::

:::theorem "eigenvalue-multiplicative" (lean := "HeckeRing.GL2.eigenform_coeff_multiplicative_one")
For a normalised eigenform the eigenvalue system is _multiplicative_: the Fourier
coefficients satisfy
$$`a_m a_n = \sum_{d \mid (m,n)} d^{k-1}\,\chi(d)\, a_{mn/d^2},`
so $`a_{mn} = a_m a_n` whenever $`\gcd(m, n) = 1` ({uses "eigenform"}[]). Following Miyake
Theorem 4.5.4(3).
:::

:::proof "eigenvalue-multiplicative"
Apply the divisor-sum Fourier formula for $`T_m T_n` ({uses "coeff-action"}[]) to a
normalised eigenform and read off the first coefficient; the multiplicativity of the
$`T_n` ({uses "hecke-commute"}[]) turns the operator identity into the stated relation on
coefficients.
:::

# The coefficient–eigenvalue relation

:::theorem "coeff-action" (lean := "HeckeRing.GL2.fourierCoeff_heckeT_n_period_one")
The $`n`-th Hecke operator acts on $`q`-expansions by the divisor-sum formula
$$`a_m(T_n f) = \sum_{d \mid (m,n)} d^{k-1}\,\chi(d)\, a_{mn/d^2}(f) \qquad (\gcd(n,N)=1),`
for $`f \in M_k(N, \chi)` ({uses "hecke-operator-tn"}[], {uses "hecke-character-space"}[]).
Following Miyake Theorem 4.5.3.
:::

:::proof "coeff-action"
The formula is proved one prime power at a time: for $`T_p` it reads
$`a_m(T_p f) = a_{pm}(f) + \chi(p)\,p^{k-1} a_{m/p}(f)`, and the prime-power and coprime
cases are assembled by the multiplicativity of $`T_n` and a divisor-sum convolution
identity.
:::

:::theorem "coeff-eigenvalue" (lean := "HeckeRing.GL2.Eigenform.coeff_eq_coeff_one_mul_eigenvalue, HeckeRing.GL2.Newform.eigenvalue_eq_coeff")
The Fourier coefficients of an eigenform are recovered from its eigenvalues and its first
coefficient ({uses "eigenform"}[]):
$$`a_n(f) = a_1(f)\, \lambda_n \qquad (\gcd(n, N) = 1).`
For a normalised newform ($`a_1 = 1`) this is simply $`\lambda_n = a_n(f)`. _(Miyake
Lemma 4.5.15(1).)_
:::

:::proof "coeff-eigenvalue"
Read off the first coefficient ($`m = 1`) of $`T_n f = \lambda_n f` using the divisor-sum
formula ({uses "coeff-action"}[]): the only surviving divisor term at $`m = 1` is
$`d = 1`, giving $`a_n(f) = \lambda_n\, a_1(f)`.
:::

:::theorem "coeff-one-ne-zero" (lean := "HeckeRing.GL2.coeff_one_ne_zero_of_mem_cuspFormsNew_of_eigen")
A nonzero common eigenfunction in the new subspace has nonvanishing leading coefficient,
$`a_1 \ne 0` ({uses "eigenform"}[], {uses "cusp-forms-new-old"}[]). _(Miyake Lemma 4.6.11.)_
:::

:::proof "coeff-one-ne-zero"
By contraposition: if $`a_1(g) = 0` then by {uses "coeff-eigenvalue"}[] every coprime
coefficient vanishes, $`a_n(g) = a_1(g)\,\lambda_n = 0`, as does $`a_0` by cuspidality. A
form with all coefficients away from $`N` vanishing lies in the old subspace
({uses "main-lemma"}[]); but $`g` is also new, and the new and old subspaces meet only in
$`0` ({uses "old-new-disjoint"}[]), forcing $`g = 0`.
:::

# Degeneracy maps and the old/new decomposition

:::definition "level-raise" (lean := "HeckeRing.GL2.levelRaise, HeckeRing.GL2.levelInclude_cusp")
For a divisor $`M \mid N` and $`\ell` with $`\ell M = N`, the _degeneracy / level-raising
map_ $`V_\ell : f \mapsto f(\ell z)` carries $`S_k(\Gamma_1(M))` into $`S_k(\Gamma_1(N))`
($`\texttt{levelRaise}`); the case $`\ell = 1` is the inclusion
$`\texttt{levelInclude\_cusp}`. Iterated level-raises compose,
$`V_{d} \circ V_{e} = V_{de}`. Following Miyake §4.6 (Lemma 4.6.2).
:::

:::theorem "level-raise-eigen" (lean := "HeckeRing.GL2.heckeT_n_levelRaise_eigen")
The level-raise of a $`T_n`-eigenform ($`\gcd(n, N) = 1`) is again a $`T_n`-eigenform with
the _same_ eigenvalue ({uses "eigenform"}[], {uses "level-raise"}[]): if $`T_n h = \lambda h`
at level $`M`, then $`T_n(V_\ell h) = \lambda\,(V_\ell h)` at level $`N`. _(Miyake Lemma
4.6.2.)_
:::

:::proof "level-raise-eigen"
The Hecke operators at the good primes commute with the degeneracy maps, so
$`T_n(V_\ell h) = V_\ell(T_n h) = V_\ell(\lambda h) = \lambda\,(V_\ell h)`.
:::

:::definition "cusp-forms-new-old" (lean := "HeckeRing.GL2.cuspFormsOld, HeckeRing.GL2.cuspFormsNew")
The _old subspace_ $`S_k^{\flat}(N)` ($`\texttt{cuspFormsOld}`) is the span of all
degeneracy images $`V_\ell f` of cusp forms at proper divisor levels $`M \mid N`,
$`M \ne N`, $`\ell > 1` ({uses "level-raise"}[]); the _new subspace_ $`S_k^{\sharp}(N)`
($`\texttt{cuspFormsNew}`) is its Petersson-orthogonal complement
({uses "petersson"}[]). Following Miyake §4.6.
:::

:::definition "petersson" (lean := "HeckeRing.GL2.petN_self_re_nonneg, HeckeRing.GL2.eigenforms_orthogonal_of_ne_eigenvalues")
The _Petersson inner product_ $`\langle f, g \rangle` is the $`\Gamma`-invariant
integral pairing on cusp forms; it is positive definite ($`\langle f, f \rangle = 0
\Rightarrow f = 0`). Two common eigenfunctions in the same Nebentypus space with
_different_ $`T_n`-eigenvalues at some $`\gcd(n, N) = 1` are Petersson-orthogonal, hence
linearly independent ({uses "eigenform"}[]). Following Miyake §4.5.
:::

:::definition "old-new-part" (lean := "HeckeRing.GL2.oldPart, HeckeRing.GL2.newPart")
Since $`S_k(\Gamma_1(N)) = S_k^{\flat}(N) \oplus S_k^{\sharp}(N)` is an orthogonal direct
sum ({uses "cusp-forms-new-old"}[]), every cusp form $`f` decomposes uniquely as
$`f = \operatorname{old}(f) + \operatorname{new}(f)`. The _old part_ $`\texttt{oldPart}`
and _new part_ $`\texttt{newPart}` are the projections onto the two summands.
:::

:::theorem "old-new-disjoint" (lean := "HeckeRing.GL2.cuspFormsOld_disjoint_cuspFormsNew, HeckeRing.GL2.cuspFormsOld_isCompl_cuspFormsNew")
The old and new subspaces are complementary: they are disjoint and together span
$`S_k(\Gamma_1(N))` ({uses "cusp-forms-new-old"}[], {uses "petersson"}[]).
:::

:::proof "old-new-disjoint"
Disjointness is immediate from positive definiteness of the Petersson form: a form in
both is orthogonal to itself, hence zero. Complementarity follows by applying the
orthogonal-complement theory of the non-degenerate Petersson form on the
finite-dimensional cusp space, giving $`S_k^{\sharp}(N) = (S_k^{\flat}(N))^{\perp}` as a
genuine complement.
:::

:::theorem "old-part-hecke-comm" (lean := "HeckeRing.GL2.oldPart_heckeT_n_cusp_comm, HeckeRing.GL2.oldPart_isEigen_of_eigenform")
The old projection commutes with every $`T_n` ($`\gcd(n,N)=1`) and with the diamond
operators ({uses "old-new-part"}[], {uses "hecke-commute-diamond"}[]); consequently the
old part of an eigenform is again an eigenform with the _same_ eigenvalues. _(Miyake
4.6.10.)_
:::

:::proof "old-part-hecke-comm"
Both subspaces are $`T_n`- and $`\langle d \rangle`-stable, so the projection along the
decomposition commutes with each operator. Applying this to an eigenform and using
$`T_n(\operatorname{old} g) = \operatorname{old}(T_n g) = \operatorname{old}(\lambda_n g)
= \lambda_n \operatorname{old} g` gives the eigen-claim.
:::

:::theorem "old-space-eigen-normal-form" (lean := "HeckeRing.GL2.exists_levelRaise_eigen_decomposition_of_mem_cuspFormsOldChar")
Every element of the ($`\chi`-refined) old space is a finite sum of level-raises
$`V_\ell h` of _new eigenforms_ $`h` at proper divisor levels $`M`, each carrying its own
level-$`M` Nebentypus character ({uses "cusp-forms-new-old"}[], {uses "level-raise"}[],
{uses "eigenform-decomp"}[]). This is the descent normal form. _(Miyake Lemma 4.6.9(3).)_
:::

:::proof "old-space-eigen-normal-form"
Induct over the span generators of the old space. Each generator is $`V_\ell` of a new
form at a proper divisor; decompose that new form into character pieces and then, by
{uses "eigenform-decomp"}[], into new eigenform summands. Level-raising is additive, so the
generator becomes a sum of level-raised new eigenforms with tracked characters.
:::

:::theorem "old-space-isotypic-identification" (lean := "HeckeRing.GL2.cuspFormsOld_inf_charSpace_le_cuspFormsOldChar, HeckeRing.GL2.cuspFormsOldChar_le_cuspFormsOld")
On the $`\chi`-isotypic part the project's degeneracy-defined old space coincides with
Miyake's character-refined old space (span of $`V_\ell`-images of _new_ spaces at
conductor-divisible levels) ({uses "cusp-forms-new-old"}[], {uses "char-space-decomp"}[]).
This identification makes the constant-multiple form of Strong Multiplicity One
unconditional. _(Miyake Lemma 4.6.4, 4.6.9.)_
:::

:::proof "old-space-isotypic-identification"
One inclusion is direct. For the reverse: rewrite the old space in the recursive normal
form (span of $`V_\ell` of new spaces) using level-raise associativity; refine each
generator to a single character at its own level; then on the $`\chi`-isotypic part the
character-space independence ({uses "char-space-decomp"}[]) collapses the sum to the
matching-character pieces, whose source levels are conductor divisible by Miyake 4.6.4.
:::

# Multiplicity one (the Main Lemma)

:::theorem "main-lemma" (lean := "HeckeRing.GL2.mainLemma_charSpace_routeB")
_(Main Lemma — Miyake Theorem 4.6.8.)_ A cusp form in $`S_k(N, \chi)` whose Fourier
coefficients $`a_n` vanish for _all_ $`n` coprime to $`N` lies in the old subspace
$`S_k^{\flat}(N)` ({uses "hecke-character-space"}[], {uses "cusp-forms-new-old"}[]). This
is the engine of the whole theory: it converts "almost all coefficients vanish" into a
structural conclusion.
:::

:::proof "main-lemma"
This is the per-character form of Miyake Theorem 4.6.8. Vanishing of all coprime
coefficients lets one run the squarefree descent (peel off one prime at a time via the
$`V_p`/$`U_p` degeneracy maps and the conductor dichotomy 4.6.4), expressing the form as a
same-level sum of degeneracy images of lower-level forms — i.e. an oldform.
:::

:::definition "newform" (lean := "HeckeRing.GL2.Newform")
A _newform_ of level $`\Gamma_1(N)` and weight $`k` is an eigenform lying in the new
subspace and normalised so that its first Fourier coefficient is $`a_1 = 1`
({uses "eigenform"}[], {uses "cusp-forms-new-old"}[]). In `LeanModularForms` this is the
structure $`\texttt{Newform}`, extending $`\texttt{Eigenform}` with the new-membership and
normalisation fields. Following Miyake §4.6.
:::

:::theorem "newform-not-old" (lean := "HeckeRing.GL2.newform_notMem_cuspFormsOldExtended")
A nonzero newform at level $`N` does not lie in the (extended) old subspace
({uses "newform"}[], {uses "cusp-forms-new-old"}[]). Its eigenvalue system is genuinely of
level $`N`, occurring at no proper divisor.
:::

:::proof "newform-not-old"
A newform lies in the new subspace, which meets the old subspace only in $`0`
({uses "old-new-disjoint"}[]); a nonzero new form therefore cannot be old.
:::

# Strong multiplicity one

:::theorem "new-part-eq-smul" (lean := "HeckeRing.GL2.newPart_eq_smul_of_shared_eigenvalues")
_(New-part identity — Miyake 4.6.12, new part.)_ If $`f` is a normalised newform and
$`g^{(1)}` is a common eigenfunction in the new subspace of $`S_k(N, \chi)` sharing $`f`'s
eigenvalues off a finite set, then $`g^{(1)} = a_1(g^{(1)})\, f`
({uses "newform"}[], {uses "coeff-eigenvalue"}[], {uses "coeff-one-ne-zero"}[]).
:::

:::proof "new-part-eq-smul"
If $`g^{(1)} = 0` this is trivial; otherwise $`b_1 = a_1(g^{(1)}) \ne 0` by
{uses "coeff-one-ne-zero"}[]. Sharing eigenvalues off a finite set forces _all_ coprime
eigenvalues to agree (propagated by multiplicativity, {uses "eigenvalue-multiplicative"}[]).
Then $`h = b_1^{-1} g^{(1)} - f` has $`a_n(h) = \lambda_n - \lambda_n = 0` for all
$`\gcd(n, N) = 1` ({uses "coeff-eigenvalue"}[] with $`a_1(f) = 1`), so $`h` is old by
{uses "main-lemma"}[]; being a difference of new forms it is also new, hence $`h = 0`.
:::

:::theorem "old-part-vanishing" (lean := "HeckeRing.GL2.oldPart_eq_zero_of_shared_eigenvalues")
_(Old-part vanishing — Miyake 4.6.12, steps (i)–(ii).)_ If $`f` is a nonzero newform and
$`g^{(2)}` is a common eigenfunction in the ($`\chi`-refined) old subspace sharing $`f`'s
eigenvalues off a finite set, then $`g^{(2)} = 0`
({uses "newform"}[], {uses "old-space-eigen-normal-form"}[], {uses "newform-not-old"}[]).
:::

:::proof "old-part-vanishing"
Suppose $`g^{(2)} \ne 0`. Write it in the descent normal form
({uses "old-space-eigen-normal-form"}[]) as a sum of level-raised new eigenforms; the
summands whose eigenvalues differ from $`f`'s are Petersson-orthogonal
({uses "petersson"}[]) and drop out, leaving a nonzero new eigenform $`h` at a proper
divisor sharing $`f`'s eigenvalues. Its leading coefficient is nonzero
({uses "coeff-one-ne-zero"}[]), so $`h` minus a scalar multiple of $`f` has vanishing
coprime coefficients hence is old ({uses "main-lemma"}[]); but $`h` is old and $`f` is not
({uses "newform-not-old"}[]), a contradiction.
:::

:::theorem "smo-const-mul" (lean := "HeckeRing.GL2.strongMultiplicityOne_constMul")
_(Strong multiplicity one, constant-multiple form — Miyake Theorem 4.6.12.)_ Let $`f` be a
normalised newform in $`S_k(N, \chi)` and $`g` any cusp-form Hecke eigenfunction in
$`S_k(N, \chi)`. If $`f` and $`g` share the eigenvalue $`\lambda_n` for all but finitely
many $`\gcd(n, N) = 1`, then $`g = c\, f` for a single $`c \in \mathbb{C}`
({uses "newform"}[], {uses "new-part-eq-smul"}[], {uses "old-part-vanishing"}[]).
:::

:::proof "smo-const-mul"
Split $`g = g^{(1)} + g^{(2)}` along the orthogonal new/old decomposition
({uses "old-new-part"}[]). Both parts are again common eigenfunctions sharing $`f`'s
eigenvalues ({uses "old-part-hecke-comm"}[]). The new part is $`a_1(g^{(1)})\, f` by
{uses "new-part-eq-smul"}[], and the old part vanishes by {uses "old-part-vanishing"}[]
(after identifying the two old spaces on the $`\chi`-isotypic part,
{uses "old-space-isotypic-identification"}[]). Hence $`g = a_1(g)\, f`.
:::

:::theorem "strong-multiplicity-one" (lean := "HeckeRing.GL2.strongMultiplicityOne_axiom_clean")
_(Strong multiplicity one — Miyake Theorem 4.6.8 / 4.6.12.)_ Two newforms $`f, g` in the
same Nebentypus space $`S_k(N, \chi)` whose Hecke eigenvalues $`\lambda_n` agree for all
but finitely many $`n` are _equal_ ({uses "newform"}[], {uses "smo-const-mul"}[]). In
`LeanModularForms` this is the _axiom-clean_ headline
$`\texttt{strongMultiplicityOne\_axiom\_clean}`.
:::

:::proof "strong-multiplicity-one"
By {uses "smo-const-mul"}[] there is $`c` with $`g = c\, f`. Comparing first Fourier
coefficients and using that both newforms are normalised, $`1 = a_1(g) = c\, a_1(f) = c`,
so $`c = 1` and $`f = g`.
:::

# Dependency graph

{blueprint_graph}

# Progress summary

{blueprint_summary}
