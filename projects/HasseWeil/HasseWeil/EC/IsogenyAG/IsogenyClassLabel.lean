import HasseWeil.EC.IsogenyAG.IsogenyClass
import HasseWeil.EC.IsogenyAG.DualDescent

/-!
# LMFDB isogeny-class labels from a given representative table

The LMFDB label of an elliptic curve over `F` is `N.x.n` — conductor `N`, isogeny-class
letter `x`, curve number `n`. The letter `x` is, by definition, a *rank*: the position of the
curve's isogeny class among all isogeny classes of conductor `N`, in LMFDB order. Deriving that
rank from scratch needs enumeration of all curves of the conductor (Shafarevich finiteness +
Mazur's bound), which is far out of reach.

Instead — exactly as the **conductor** is taken as given input — we take the **LMFDB
isogeny-class table** of a fixed conductor as given input (`IsogenyClassTable`): the ordered
list of class representatives together with their LMFDB letter strings. Labeling a curve `E`
then reduces to an **isogeny-membership check**: `E`'s class letter is the `letter i` of the
unique table representative `reps i` that `E` is isogenous to. No enumeration, no Shafarevich.

The single mathematical fact this rests on is **well-definedness** — `E` cannot be isogenous to
two distinct representatives. That follows from `IsIsogenous` being an equivalence relation, i.e.
from **symmetry of isogeny** (every isogeny has a dual, Silverman III.6.1). Over a general field
(e.g. `ℚ`) that symmetry is the project's standing deep residual, gated on `UniversalDualWitness F`
(see `IsogenyClass.lean`); we carry the same gate here. So this layer is honest and unconditional
*modulo* the one gate the whole isogeny-class theory already depends on — and that gate, too, may
be supplied as given data alongside the conductor and the table.

This file is pure isogeny content; conductor strings and within-class curve numbers are taken as
parameters (supplied by the conductor development and the table's within-class ordering).
-/

namespace HasseWeil.EC

variable {F : Type*} [Field F] [DecidableEq F]

/-- The LMFDB isogeny-class table of a fixed conductor, **taken as given input** (exactly as the
conductor is). `reps i` is the LMFDB representative of the `i`-th isogeny class of this conductor,
in LMFDB order; `letter i` is its given LMFDB letter string (`"a"`, `"b"`, …, `"z"`, `"ba"`, …).
The representatives are pairwise non-isogenous — that is precisely what makes them *distinct*
classes. -/
structure IsogenyClassTable (F : Type*) [Field F] where
  /-- The number of isogeny classes of this conductor. -/
  card : ℕ
  /-- The representative curve of each class, in LMFDB order. -/
  reps : Fin card → EllipticCurveOver F
  /-- The LMFDB letter string of each class. -/
  letter : Fin card → String
  /-- Distinct representatives are non-isogenous (they are distinct classes). -/
  pairwise_not_isogenous :
    ∀ i j : Fin card, i ≠ j → ¬ IsogenousCurves (reps i) (reps j)

namespace IsogenyClassTable

/-- **Well-definedness of the label** (gated on isogeny symmetry): a curve is isogenous to at
most one table representative. Uses `IsIsogenous.symm_of` (the dual, Silverman III.6.1) +
transitivity + the table's pairwise non-isogeny. -/
theorem index_unique (hw : UniversalDualWitness F) (T : IsogenyClassTable F)
    (E : EllipticCurveOver F) {i j : Fin T.card}
    (hi : IsogenousCurves E (T.reps i)) (hj : IsogenousCurves E (T.reps j)) :
    i = j := by
  by_contra hne
  -- `reps i ~ E ~ reps j`, contradicting pairwise non-isogeny
  exact T.pairwise_not_isogenous i j hne ((IsIsogenous.symm_of hw hi).trans hj)

/-- The index of `E`'s isogeny class in the table, given that `E` is isogenous to *some*
representative (the "the table is complete for this conductor" assumption — supplied, like the
conductor). Well-defined by `index_unique`. -/
noncomputable def index (T : IsogenyClassTable F) (E : EllipticCurveOver F)
    (hmem : ∃ i, IsogenousCurves E (T.reps i)) : Fin T.card :=
  hmem.choose

/-- `E` is isogenous to the representative at its index. -/
theorem isogenous_index (T : IsogenyClassTable F) (E : EllipticCurveOver F)
    (hmem : ∃ i, IsogenousCurves E (T.reps i)) :
    IsogenousCurves E (T.reps (T.index E hmem)) :=
  hmem.choose_spec

/-- `index` picks out *the* index of any representative `E` is isogenous to (gated on symmetry). -/
theorem index_eq (hw : UniversalDualWitness F) (T : IsogenyClassTable F)
    (E : EllipticCurveOver F) (hmem : ∃ i, IsogenousCurves E (T.reps i))
    {i : Fin T.card} (hi : IsogenousCurves E (T.reps i)) :
    T.index E hmem = i :=
  T.index_unique hw E (T.isogenous_index E hmem) hi

/-- **The LMFDB isogeny-class letter of `E`** (the `x` in `N.x.n`), read off the given table. -/
noncomputable def classLetter (T : IsogenyClassTable F) (E : EllipticCurveOver F)
    (hmem : ∃ i, IsogenousCurves E (T.reps i)) : String :=
  T.letter (T.index E hmem)

/-- **The class letter is an isogeny invariant** (gated on symmetry): isogenous curves get the
same LMFDB letter. This is the defining property of the isogeny-class component of the label. -/
theorem classLetter_eq_of_isogenous (hw : UniversalDualWitness F) (T : IsogenyClassTable F)
    {E E' : EllipticCurveOver F} (hEE' : IsogenousCurves E E')
    (hmem : ∃ i, IsogenousCurves E (T.reps i))
    (hmem' : ∃ i, IsogenousCurves E' (T.reps i)) :
    T.classLetter E hmem = T.classLetter E' hmem' := by
  unfold classLetter
  congr 1
  -- `index E = index E'`: `E ~ E' ~ reps (index E')`, so `E` is isogenous to that rep
  exact T.index_eq hw E hmem (hEE'.trans (T.isogenous_index E' hmem'))

/-- **The full LMFDB label `N.x.n`**, assembled from the given conductor string `N` (from the
conductor development), the isogeny-class letter `x` (this file), and the within-class curve
number `n` (from the table's within-class ordering, supplied). -/
noncomputable def lmfdbLabel (T : IsogenyClassTable F) (conductor : String)
    (E : EllipticCurveOver F) (hmem : ∃ i, IsogenousCurves E (T.reps i))
    (curveNumber : ℕ) : String :=
  conductor ++ "." ++ T.classLetter E hmem ++ "." ++ toString curveNumber

/-! ### Ungated char-0 corollaries (DUAL-Q4)

Over a characteristic-`0` field the universal dual witness is a theorem
(`universalDualWitness_of_charZero`), so the symmetry gate disappears: the label well-definedness
and the class-letter invariance hold unconditionally. These are the deliverables that make the LMFDB
label layer over `ℚ` (or any char-`0` field) gate-free. -/

/-- **Well-definedness of the label, char-0 (ungated)**: over a char-`0` field a curve is isogenous to
at most one table representative — no `UniversalDualWitness` hypothesis needed
(`universalDualWitness_of_charZero`). -/
theorem index_unique_charZero [CharZero F] (T : IsogenyClassTable F)
    (E : EllipticCurveOver F) {i j : Fin T.card}
    (hi : IsogenousCurves E (T.reps i)) (hj : IsogenousCurves E (T.reps j)) :
    i = j :=
  T.index_unique (universalDualWitness_of_charZero F) E hi hj

/-- **`index` picks out the unique class index, char-0 (ungated)**. -/
theorem index_eq_charZero [CharZero F] (T : IsogenyClassTable F)
    (E : EllipticCurveOver F) (hmem : ∃ i, IsogenousCurves E (T.reps i))
    {i : Fin T.card} (hi : IsogenousCurves E (T.reps i)) :
    T.index E hmem = i :=
  T.index_eq (universalDualWitness_of_charZero F) E hmem hi

/-- **The class letter is an isogeny invariant, char-0 (ungated)**: over a char-`0` field isogenous
curves get the same LMFDB letter, unconditionally. -/
theorem classLetter_eq_of_isogenous_charZero [CharZero F] (T : IsogenyClassTable F)
    {E E' : EllipticCurveOver F} (hEE' : IsogenousCurves E E')
    (hmem : ∃ i, IsogenousCurves E (T.reps i))
    (hmem' : ∃ i, IsogenousCurves E' (T.reps i)) :
    T.classLetter E hmem = T.classLetter E' hmem' :=
  T.classLetter_eq_of_isogenous (universalDualWitness_of_charZero F) hEE' hmem hmem'

end IsogenyClassTable

end HasseWeil.EC
