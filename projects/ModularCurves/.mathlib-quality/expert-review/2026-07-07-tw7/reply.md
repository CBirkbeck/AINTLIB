# Reviewer reply — T-W7 group-law brief (received 2026-07-07, verbatim)

Yes — this T-W7 brief is **on track**, and the reduction strategy is sound in broad outline. The big picture is right: construct the group law once on the universal Weierstrass atlas, prove its identities over the universal integral base, then obtain group laws on arbitrary locally-Weierstrass families by base change and gluing. That is exactly the right way to avoid coherent cohomology on the critical path.

The most important refinements are:

1. **Do not try to get `π_* O_E = O_S` by proving it only for the universal curve and then base-changing.** Prove it uniformly for every projective Weierstrass model over every ring, by an explicit global-functions computation.

2. **Do not try to avoid rigidity for canonicity over arbitrary nonreduced bases.** Dense-open or reduced-base uniqueness will not be enough. Use a formal-friendly rigidity lemma whose proof is powered by `π_* O = O`.

3. **For the multiplication morphism, prefer an explicit open-cover/gluing construction or a graph-closure construction, not a case-split field formula.** The case split on `x₁ = x₂`, anti-diagonal, and infinity is the real danger, as the brief correctly identifies.

## Review of the overall strategy

The brief's goal is to construct, for a locally-Weierstrass smooth proper relative curve with section, an honest commutative group-scheme structure over arbitrary `S`, including possibly nonreduced `S`, and then prove uniqueness of that group structure with identity section.  This is the right target, because the full programme's definition of elliptic curve now uses locally-Weierstrass models as the definition of record, with the abstract genus-one definition postponed to a later comparison theorem.

The strategy in §3 is also sound: construct `m_U` and `ι_U` over the universal integral coefficient scheme, prove the group axioms there by generic-fibre comparison and separated-target/dense-source arguments, then descend to arbitrary bases via base change and gluing.  This is a legitimate way to avoid reducedness assumptions on the final base `S`: the density argument is used only over the universal reduced/integral atlas; after that, the group identities are transported as equalities of morphisms by base change and gluing.

The separation between **existence** and **canonicity** is important and should stay. Existence can be explicit and Weierstrass-local. Canonicity is genuinely a rigidity theorem; trying to prove it by the same generic-fibre argument over arbitrary `S` will fail over nonreduced bases.

## Q1. Multiplication morphism `m_U`

The cleanest formal route is probably **explicit open-cover-and-glue**, with a possible backup of **graph closure**.

I would not start with a single "total resultant/projective formula" unless you already have a reliable source for complete addition laws on general long Weierstrass equations over arbitrary rings. Such formulae exist in various computational literatures, but they are often optimized for special forms or require several formula charts anyway. A single formula also tends to hide base-locus issues, which are exactly what a formal proof assistant will force you to expose.

The cover-and-glue construction should cover `E_U ×_U E_U` by loci such as:

```text
1. both points affine and x₁ ≠ x₂      -- secant formula
2. diagonal away from small exceptional loci -- tangent formula
3. anti-diagonal P₂ = -P₁              -- sum is O
4. one point is O                      -- unit formulas
5. remaining projective/infinity charts
```

But I would formulate the cover in **projective chart language**, not in field-point language. The goal is not "case split on points"; it is "cover the source by open subschemes on which the relevant rational functions are regular."

A good formal pattern is:

```lean
def addOnSecantOpen : U_sec ⟶ E_U
def addOnTangentOpen : U_tan ⟶ E_U
def addOnAntiDiagonal : U_anti ⟶ E_U
def addOnLeftInfinity : U_leftO ⟶ E_U
def addOnRightInfinity : U_rightO ⟶ E_U

theorem add_pieces_cover : ...
theorem add_pieces_agree_on_overlaps : ...
def m_U : E_U ×[U] E_U ⟶ E_U := glue add_pieces
```

The overlap proofs should mostly be discharged by comparing on a dense open of each overlap where the affine formulas agree, provided the overlaps are reduced and the target is separated. Where an overlap is not reduced or not known reduced, prove equality algebraically from the formulas.

The **graph-closure alternative** is elegant but may be harder in Lean:

```text
1. Define the rational addition map on a dense open.
2. Take its graph closure Γ ⊂ E_U ×_U E_U ×_U E_U.
3. Prove Γ → E_U ×_U E_U is an isomorphism.
4. Define m_U as the composite inverse followed by projection.
```

This avoids many individual glue maps but shifts the burden to proving the graph projection is an isomorphism. That proof usually uses local computations at exactly the diagonal, anti-diagonal, and infinity loci. So I would only choose this if your existing "rational/partial maps with dense domain" infrastructure is already strong enough. The brief says such infrastructure exists, but not the graph-isomorphism machinery.

A third conceptual route is to use the complete linear system `|3O|` and define `P+Q` by the divisor relation

```text
[P] + [Q] + [-(P+Q)] ~ 3[O].
```

But that reintroduces Picard/Riemann–Roch-style geometry, which the whole locally-Weierstrass route is designed to avoid.

**Recommendation:** use explicit open-cover-and-glue. Keep the graph-closure route as a fallback, not the first implementation.

## Q2. Proving `π_* O_E = O_S`

Yes, there should be an elementary route for projective Weierstrass models, but I would **not** prove it by showing it for `E_U/U` and then invoking base change. That is exactly the kind of cohomology-and-base-change argument you are trying to avoid.

Instead prove the following directly, for every ring `R` and every elliptic Weierstrass equation `W/R`:

```text
Γ(ProjModel(W), O) ≅ R.
```

Then for a locally-Weierstrass family over a scheme `S`, the sheaf statement

```text
O_S ≅ π_* O_E
```

follows Zariski-locally on affine opens.

There are two plausible elementary proofs.

### Route A: Čech/gluing computation on the three standard charts

Use the affine cover

```text
D_+(X), D_+(Y), D_+(Z)
```

of the projective model. A global function is a triple of regular functions on the three chart rings that agree on overlaps. Show algebraically that the equalizer of the chart rings is exactly `R`.

This is probably the most formal-friendly route because your development already has a detailed three-chart construction of `ProjModel(W)` and its base-change theory. The full-programme inventory says the projective model is built as `Proj`, its structure morphism and section are implemented, the three-chart affine open cover exists, and smoothness/base-change have been proved.

### Route B: graded-ring theorem for `Γ(Proj A, O)`

For good standard graded rings, one can prove `Γ(Proj A, O) = A₀`. Here `A` is the homogeneous coordinate ring of a smooth plane cubic, and `A₀ = R`. But the general theorem has hypotheses, and proving those hypotheses may be no easier than the direct Čech computation.

So I recommend the chart computation first.

Once proved, package it as:

```lean
theorem projModel_globalSections :
  Γ(projModel W, ⊤) ≃+* R

theorem projModel_pushforward_structureSheaf :
  (projModelπ W)_* O = O_SpecR

theorem locallyWeierstrass_pushforward_structureSheaf :
  π_* O_E ≅ O_S
```

For rigidity you need the statement **universally**, i.e. after arbitrary base change. If the global-sections theorem is proved for every ring `R`, then universality follows by applying the same theorem to `W.map (R → R')`, not by an abstract cohomology base-change theorem.

## Q3. Rigidity over arbitrary base

The rigidity lemma is the right tool for canonicity. The proof can be made formal-friendly if you reduce it to two ingredients:

```text
1. properness gives closed images;
2. π_* O_X = O_S gives affine factorisation.
```

A useful statement is:

```text
Let p : X → S be proper, flat, and universally O-connected:
  O_T ≅ (p_T)_* O_{X_T}
for every T → S.

Let f : X ×_S Y → Z be an S-morphism.
If f is constant on X × {y₀}, then after shrinking Y around y₀,
f factors through Y.
```

The classical proof sketched in the brief is the right one. Choose an affine open neighbourhood `V ⊂ Z` of the constant value. The complement `Z \ V` has closed preimage in `X ×_S Y`. Its image in `Y` is closed because `X ×_S Y → Y` is proper. Since this closed image misses `y₀`, shrink `Y` so that `f` lands in `V`. Now a map to affine `V = Spec A` is a ring map

```text
A → Γ(X ×_S Y, O).
```

But universal `π_*O=O` gives

```text
Γ(X ×_S Y, O) = Γ(Y, O)
```

locally on affine `Y`. Hence the map factors through `Y`.

Then the corollary "pointed morphisms of abelian schemes are homomorphisms" follows by applying rigidity to

```text
h(x,y) = f(x+y) - f(x) - f(y).
```

Since `f(0)=0`, `h` is zero on `X × {0}` and `{0} × Y`; rigidity first makes it factor through one projection, then the second restriction forces the factor to be zero.

I would not assume the base is reduced or normal for canonicity. Over nonreduced bases, two morphisms can agree on the reduced subscheme and differ by nilpotents. A reduced-base uniqueness theorem will not automatically give uniqueness over arbitrary bases. Since the goal explicitly includes arbitrary schemes, including nonreduced ones, and group laws are identities of `S`-morphisms, the arbitrary-base rigidity lemma is the right target.

Faltings–Chai citing rigidity for abelian schemes is useful background, but for this project I would build the narrow rigidity lemma directly from the proof above, not import a large abelian-schemes theory. The brief notes that Faltings–Chai use rigidity to deduce commutativity and discuss abelian schemes as smooth proper group schemes with connected fibres.

## Q4. Generic-fibre bridge and integrality

The generic-fibre bridge is sound, but it needs to be stated carefully.

For `m_U|_K =` field chord-tangent addition, do not try to compare the scheme morphism with the abstract group operation only on `K`-points. Instead prove a morphism-level statement:

```text
On the dense secant open of E_K × E_K,
the morphism m_U base-changed to K is given by the same coordinate functions
as the field-level chord–tangent formula.
```

Then use density/separatedness over the field to conclude equality with the field-level addition morphism, assuming the field-level library has addition as a morphism or at least has a scheme morphism representing it. If the field-level library only gives a group law on points, then you need an intermediate theorem:

```text
The explicit field addition morphism represents the library's pointwise group law
on every field extension L/K.
```

Checking only on `{x₁ ≠ x₂}` should be enough if:

```text
E_K ×_K E_K is integral,
the secant open is dense,
the target E_K is separated,
and both morphisms are defined everywhere.
```

For integrality, the clean lemma is:

```text
If S is integral and f : X → S is smooth with geometrically integral fibres,
then X is integral.
```

Then apply it to `E_U → U`, and again to fibre products:

```text
E_U ×_U E_U → U,
E_U ×_U E_U ×_U E_U → U,
...
```

because products of geometrically integral varieties over a field are geometrically integral. You may only need reduced + topologically irreducible, but "integral" is the cleanest API.

If that general lemma is too far away, prove a specialized version:

```text
E_U is integral by chart/ring computation;
E_U^n is integral because the generic fibre is integral and the map is smooth/flat
with integral base.
```

But the general smooth-geometrically-integral-fibres lemma will be reusable later.

## Q5. Soundness of the universal reduction

The reduction is sound, with three caveats.

First, the multiplication `m_U` must be a genuine global morphism before the generic-fibre proof of the axioms begins. A rational map or partially defined map is not enough.

Second, variable-change invariance must be upgraded from "affine formulas agree" to **equivariance of the global morphism**:

```text
m_U(gP, gQ) = g m_U(P,Q)
```

for the Weierstrass coordinate-change group. The brief says the affine addition formulas and negation are invariant under variable changes and that this gives cocycle compatibility.  Make sure the final theorem is global, including infinity, diagonal, and anti-diagonal cases.

Third, when gluing over a locally-Weierstrass family `E/S`, use an explicit atlas or affine open cover object, not only the pointwise `∀ s, ∃ U` predicate. The pointwise predicate is fine as a public definition, but for construction you want a bundled cover:

```lean
structure WeierstrassAtlas (E S) where
  I : Type
  U : I → S.affineOpens
  covers : ...
  W : ∀ i, WeierstrassCurve Γ(S, U i)
  iso : ∀ i, E|_{U i} ≅ ProjModel (W i)
  pointed : ...
```

Then prove that the pointwise `LocallyWeierstrass` predicate gives such an atlas after choosing refinements. This will make descent/gluing much cleaner.

The non-flatness of the classifying map `S → U` is not a problem: base change of a morphism and of an identity of morphisms does not require flatness. It would only matter if you were trying to infer properties like reducedness or density after base change, which you are not.

## Q6. Alternative to rigidity for uniqueness

I would not rely on a dense-open uniqueness argument for canonicity. It will not survive nonreduced bases.

A typical failure mode is that two morphisms

```text
X → Y
```

can agree on the reduced subscheme `X_red` and still differ by nilpotent functions. A graph-closedness argument also does not rule this out; separatedness makes equalizers closed, but a closed subscheme containing the underlying topological space need not be all of a nonreduced scheme.

So the right answer is:

```text
Existence: explicit Weierstrass construction and gluing.
Canonicity: rigidity via universal π_*O = O.
```

If canonicity is not immediately needed for downstream level structures, you can postpone it. But if the definition of `EllipticCurve` stores group law as data and you want to prove "this data is canonical," then rigidity is the robust proof.

## Additional improvement: split "existence of group law" from "purity of definition"

I would name two milestones:

```text
T-W7a:
  Constructive group law on every locally-Weierstrass family by atlas descent.

T-W7b:
  Canonicity of any group law with identity e, via π_*O=O and rigidity.
```

Then the critical path to torsion and level structures only needs T-W7a. T-W7b is important for API cleanliness and future comparison with the abstract genus-one definition, but it should not block `E[N]`, Drinfeld structures, or `Y(N)`.

## Additional improvement: prove `π_*O=O` before rigidity but after `m_U`

Do not put `π_*O=O` before construction of `m_U`. It is not needed for existence. The efficient order is:

```text
1. Build m_U and inverse on the universal model.
2. Prove group identities over U by generic fibre + separatedness.
3. Descend existence to locally-Weierstrass families.
4. Prove Γ(ProjModel(W), O) = R by chart computation.
5. Deduce universal π_*O=O for locally-Weierstrass families.
6. Prove rigidity.
7. Deduce canonicity.
```

This keeps the difficult but independent rigidity machinery from blocking construction.

## Concrete answers to the six reviewer questions

**Q1.** Prefer explicit open-cover/glue for `m_U`. A total resultant formula is attractive but risky unless sourced. Graph closure is elegant but may be harder than gluing because you still must prove the graph projection is an isomorphism.

**Q2.** Yes, prove `π_*O=O` elementarily for projective Weierstrass models. Do it uniformly over every ring by a three-chart global-functions computation. Do not prove it only over `U` and base-change.

**Q3.** Use the rigidity lemma. Its formal proof should reduce to proper closed-image + affine factorisation using `π_*O=O`. Do not reduce to normal or reduced bases if you want canonicity over arbitrary schemes.

**Q4.** State the generic-fibre bridge as equality of morphisms after base change to `K`, first on a dense secant open, then globally by separatedness. Prove integrality via "smooth over integral base with geometrically integral fibres."

**Q5.** The universal-atlas reduction is sound. The key pitfall is ensuring variable-change invariance is a global morphism-level equivariance theorem, not merely an affine formula theorem.

**Q6.** No reliable alternative to rigidity for arbitrary nonreduced bases. Dense-open uniqueness and graph-closedness are not enough. Use rigidity for canonicity, or postpone canonicity while using the constructed group law.

## Bottom line

Proceed with T-W7. The plan is mathematically sound, but I would sharpen the implementation path:

```text
m_U by explicit open-cover/glue;
axioms over U by generic fibre;
existence over S by base change and atlas gluing;
Γ(ProjModel(W),O)=R by chart computation;
rigidity from π_*O=O;
canonicity from rigidity.
```

This keeps the constructive Weierstrass path free of coherent cohomology while still giving a fully scheme-level group law and a robust uniqueness theorem over arbitrary bases.
