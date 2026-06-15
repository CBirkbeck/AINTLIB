import Verso
import VersoManual
import VersoBlueprint
import LeanModularForms.Modularforms.DimensionFormulas

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Dimension formulas and finite-dimensionality" =>

Spaces of modular forms are finite-dimensional, and at level one their dimensions are
governed by mathlib's level-one dimension formula. The project carries two parallel
descriptions of the level-one situation: one phrased through the congruence subgroup
$`\Gamma(1)`, the other through $`\mathrm{SL}_2(\mathbb{Z})` viewed as a subgroup of
$`\mathrm{GL}_2^{+}(\mathbb{R})`; this chapter records the explicit linear equivalence
identifying the two. From it one reads off that cusp forms of weight below $`12` vanish, and,
for a general congruence subgroup of finite index, finite-dimensionality follows by a
norm-reduction argument transporting forms back to the level-one space.

:::definition "level-one-equiv" (lean := "modularFormGammaOneEquivSL, cuspFormGammaOneEquivSL")
*Level-one forms: $`\Gamma(1)` versus $`\mathrm{SL}_2(\mathbb{Z})`.*
Fix a weight $`k`. The space of modular forms of weight $`k` for the congruence subgroup
$`\Gamma(1)` and the space of modular forms of weight $`k` for $`\mathrm{SL}_2(\mathbb{Z})`,
regarded as a subgroup of $`\mathrm{GL}_2^{+}(\mathbb{R})`, are linearly equivalent over
$`\mathbb{C}`. The same holds for the corresponding spaces of cusp forms. Both equivalences are
the identity on the underlying functions: a form is sent to the form computing the same value at
every point $`z` of the upper half-plane, and only the bookkeeping of the modularity condition is
transported, along the equality of subgroups identifying $`\Gamma(1)` with
$`\mathrm{SL}_2(\mathbb{Z})`. Because the maps act trivially on functions they are visibly
additive, commute with scalar multiplication, and are mutually inverse, so each is an isomorphism
of $`\mathbb{C}`-vector spaces. These identifications let the level-one dimension and rank
results stated on the $`\mathrm{SL}_2(\mathbb{Z})` side be read back onto the $`\Gamma(1)` side.
:::

:::theorem "findim-congruence" (lean := "dim_gen_cong_levels")
*Finite-dimensionality for finite-index subgroups.*
Let $`k` be a weight and let $`\Gamma` be a subgroup of $`\mathrm{SL}_2(\mathbb{Z})` of finite
index, that is, with nonzero index. Then the space of modular forms of weight $`k` for $`\Gamma`
is finite-dimensional over $`\mathbb{C}`.
:::

:::proof "findim-congruence"
The cases of nonpositive weight are handled separately: in negative weight the space is trivial,
and in weight $`0` every form is constant, so the space is one-dimensional. For positive weight
the argument proceeds by reduction to level one. To a form $`f` for $`\Gamma` one associates its
*norm* to level one, the product over the finitely many cosets of $`\Gamma` in
$`\mathrm{SL}_2(\mathbb{Z})` of the translates of $`f` by coset representatives. This
symmetrisation is invariant under all of $`\mathrm{SL}_2(\mathbb{Z})`, so it is a modular form of
weight $`k\cdot[\mathrm{SL}_2(\mathbb{Z}):\Gamma]` for the full level-one group, and it vanishes
exactly when $`f` does, since $`f` itself occurs as one of its factors.

The space of level-one forms of that weight is finite-dimensional, and a stabilisation argument for
descending chains of subspaces shows that finitely many of the coefficients in the expansion at the
cusp $`\infty` already determine a level-one form. Transferring this through the norm — vanishing of
the first $`N` such coefficients of $`f` forces the corresponding coefficients of its norm to vanish
— the linear map sending each form for $`\Gamma` to its first $`N` cusp-expansion coefficients is
injective. This realises the space of forms for $`\Gamma` as a subspace of the finite-dimensional
coordinate space $`\mathbb{C}^{N}`, whence it is itself finite-dimensional.
:::

:::theorem "cuspform-weight-lt-12" (lean := "cuspform_weight_lt_12_zero")
*Vanishing of low-weight cusp forms at level one.*
Fix a weight $`k` with $`k < 12`. Then the space of cusp forms of weight $`k` for the congruence
subgroup $`\Gamma(1)` is the zero space; equivalently, its rank over $`\mathbb{C}` is $`0`.
:::

:::proof "cuspform-weight-lt-12"
Through the linear equivalence identifying cusp forms of weight $`k` for $`\Gamma(1)` with cusp
forms of weight $`k` for $`\mathrm{SL}_2(\mathbb{Z})`, the assertion is transported to the
corresponding statement on the $`\mathrm{SL}_2(\mathbb{Z})` side, where it is known: cusp forms of
weight below $`12` for the full modular group form the zero space. That fact rests on the valence
formula. A nonzero cusp form of weight $`k` vanishes at the cusp $`\infty`, contributing at least
one to the total order of vanishing; but the valence formula bounds the weighted count of zeros by
$`k/12`, which is less than one when $`k < 12`. Equivalently, any such cusp form is divisible by the
weight-$`12` discriminant $`\Delta`, producing a holomorphic form of negative weight, which must
vanish. Since rank is preserved by linear equivalence, the $`\Gamma(1)` space is likewise of rank
$`0`.

Depends on: {uses "level-one-equiv"}[]
:::

:::theorem "low-weight-one-dimensional" (lean := "weight_four_one_dimensional, weight_six_one_dimensional")
*Weight $`4` and weight $`6` level-one forms are one-dimensional.*
The spaces of modular forms of weight $`4` and of weight $`6` for the congruence subgroup
$`\Gamma(1)` are each one-dimensional over $`\mathbb{C}`; that is, both have rank $`1` as
$`\mathbb{C}`-vector spaces.
:::

:::proof "low-weight-one-dimensional"
Through the linear equivalence identifying weight-$`k` modular forms for $`\Gamma(1)` with
weight-$`k` modular forms for $`\mathrm{SL}_2(\mathbb{Z})`, the two assertions reduce to the
corresponding rank computations on the $`\mathrm{SL}_2(\mathbb{Z})` side. There, for each of the
weights $`4` and $`6` the full modular group carries a distinguished nonzero form, namely the
Eisenstein series $`E_4` of weight $`4` and $`E_6` of weight $`6`. Given any modular form of
weight $`4` (respectively $`6`), subtracting the multiple of $`E_4` (respectively $`E_6`) matching
its value at the cusp $`\infty` produces a form vanishing there, hence a cusp form of weight below
$`12`; such a cusp form is zero. Thus every form is a scalar multiple of the corresponding
Eisenstein series, so each space is spanned by a single nonzero element and has rank $`1`. Since
rank is preserved by the linear equivalence, the same holds for the $`\Gamma(1)` spaces.

Depends on: {uses "level-one-equiv"}[]
:::
