# Review brief — Adic spaces / Wedhorn Theorem 8.28(b) Čech-acyclicity route

*Prepared 2026-05-28 for a senior algebraic geometer / LLM reviewer.
Self-contained: no repository access required. Uses Wedhorn (2019, arXiv:1910.05934)
notation throughout, in particular `Spa(A, A⁺)`, `R(T/s)`, `𝒪_X`, `A⟨ζ⟩`,
chapter numbering 6.X / 7.X / 8.X.*

This brief is **narrow scope**: it surfaces two specific stuck points from the
project's current frontier and asks for mathematical guidance on each. The
project as a whole is substantially larger; §3 sketches the strategic context
the two stuck points live in, but the actual ask is the two questions in §9.

This is the latest round of consultation on the Adic spaces project. Earlier
rounds (2026-05-11 to 2026-05-27) produced the Route C / Banach OMT scaffold
for the embedding clause of sheafiness and reframed the proof strategy after
identifying a defect in the original Huber Wedhorn 8.15 route. The current
round is much narrower: only the two specific questions surfaced by the
2026-05-28 `/develop --continue` audit.

---

## 1. Goal

We are formalising, in Lean 4 / Mathlib, **Wedhorn's Theorem 8.28(b)** in the
following form: every *strongly noetherian Tate ring* `A` is *sheafy*, i.e. the
presheaf `𝒪_X` on `X := Spa(A, A⁺)` (defined on the basis of rational subsets
by `𝒪_X(R(T/s)) := A⟨T/s⟩` and extended to all open subsets by left-Kan limit)
is a sheaf.

The headline theorem in the project carries no per-cover hypothesis. Its
hypotheses are exactly the textbook hypotheses of Wedhorn 8.28(b):
strongly-noetherian Tate (with the principal pair-of-definition data), plus
the standard typeclass scaffolding (`IsDomain`, `T2Space`, `NonarchimedeanRing`,
`HasLocLiftPowerBounded`, `CompatiblePlusSubring`) that the project uses to
encode the analytic content of Tate algebras.

We follow Wedhorn's **§8.3 Čech-acyclicity route**: Cor 8.32 (faithful flatness)
plus Lemma 8.33 (2-cover Čech exactness) plus Lemma 8.34 (rational-cover
acyclicity) plus Prop A.3 (acyclicity transfer along refinements) plus Lemma 7.54
(rational-cover refinement) plus Cor 7.32 (dominating unit) plus Wedhorn 6.18
(noetherian pair-subring) plus Wedhorn 7.40(6) (analytic ⇒ height ≤ 1) plus
Examples 6.38/6.39 (Laurent algebra identifications). This is a different route
from Huber's original 8.15 (Baire surjection), which the project tried earlier
and abandoned after a reviewer flagged it as targeting a mathematically false
statement (see §2.3).

---

## 2. Background and references

### 2.1 Setting and notation

We work with Huber's adic spectrum:

- `A` is a Tate ring over `ℤ` with a chosen pair of definition `(A₀, I)`.
  *Strongly noetherian* means `A⟨X₁,…,Xₙ⟩` is noetherian for all `n ≥ 0`. The
  project carries the principal pair `(A₀, (s))` for a fixed topologically
  nilpotent unit `s`.
- `A⁺` is a ring of integral elements (an open and integrally closed subring of
  the power-bounded subring `A°`).
- `X := Spa(A, A⁺) := {equivalence classes of continuous valuations v on A
  with v(a) ≤ 1 for a ∈ A⁺}`.
- For `T ⊆ A` finite and `s ∈ A` such that `T · A = ⟨T⟩ = A` and `s ∈ T`, the
  *rational subset* `R(T/s) ⊆ X` is `{v ∈ X : v(t) ≤ v(s) ≠ 0 for all t ∈ T}`.
  We write `D` for a *rational location datum* `(T, s, hopen)` where `hopen`
  packages the openness `T · A = A`, etc.
- `𝒪_X(R(T/s)) := A⟨T/s⟩`, the completion of `A[1/s]` for the topology making
  `T/s` power-bounded. Concretely the project uses `presheafValue D :=
  UniformSpace.Completion (Localization.Away D.s)` with the localization
  topology.
- `canonicalMap` is the structural ring homomorphism `A → 𝒪_X(R(T/s))`. For
  `t ∈ T`, `canonicalMap t / canonicalMap s` is a unit in `𝒪_X(R(T/s))` by
  construction; for `t ∉ T`, no such guarantee.
- A *rational covering* `𝒰 = (U_t)_{t ∈ T}` of a rational subset `Y` is a finite
  family of rational subsets `U_t ⊆ Y` whose pointwise union is `Y`.

The project's `RationalCovering A` is the bundle of `(base : RationalLocData A,
covers : Finset (RationalLocData A), hsubset : ∀ D ∈ covers, R(D.T/D.s) ⊆ R(base.T/base.s),
hcover : ∀ v ∈ R(base.T/base.s), ∃ D ∈ covers, v ∈ R(D.T/D.s))`.

A *Čech-acyclic* cover (Wedhorn's `𝒪_X-acyclic`, project's `IsOXAcyclic`) is one
for which the augmented Čech complex with alternating cochains for the cover is
exact. The project uses the **0-cohomology form**, namely *separation* +
*gluing*: `IsOXAcyclic C` has fields

- `separation` — `∀ x ∈ presheafValue C.base, (∀ D ∈ C.covers, x|_D = 0) ⇒ x = 0`
- `gluing` — `∀ f : ∀ D ∈ C.covers, presheafValue D, (compatibility on
  intersections) ⇒ ∃ x ∈ presheafValue C.base, ∀ D ∈ C.covers, x|_D = f D`

Compatibility is taken on arbitrary refined pieces `D₃ ⊆ D₁ ∩ D₂` rather than
on intersections, which gives a cleaner shape for the `RationalLocData`
formalism (no need to construct an explicit intersection datum).

### 2.2 References

The single primary source is Wedhorn's *Adic Spaces* preprint.

> [Wedhorn19] Torsten Wedhorn. *Adic Spaces.* arXiv:1910.05934v1, 2019.
> 154 pp.

Secondary sources cited at various points:

> [Huber94] Roland Huber. "A generalization of formal schemes and rigid analytic
> varieties." Mathematische Zeitschrift 217 (1994), 513–551.
>
> [BGR] Siegfried Bosch, Ulrich Güntzer, Reinhold Remmert. *Non-Archimedean
> Analysis: A Systematic Approach to Rigid Analytic Geometry.* Grundlehren der
> mathematischen Wissenschaften 261. Springer, 1984. (Used for Banach-OMT
> material that the project ended up routing around.)
>
> [Bourbaki-CA-III] N. Bourbaki, *Algèbre commutative*, ch. III. (Cited at one
> point for an alternative Prop A.3(2) bridge; not currently on the active
> path.)

### 2.3 State of the art

Theorem 8.28(b) is classical and stated in Wedhorn essentially as we use it.
The novel thing about this project is the Lean 4 / Mathlib formalisation, not
the mathematical content.

Earlier in the project (2026-02 to 2026-04) we tried Huber's original strategy
via Wedhorn's Proposition 8.15 ("the restriction map `𝒪_X(D₀) → 𝒪_X(D_i)` is
a localisation at the relevant power"). An external reviewer (ChatGPT Pro,
2026-05-11) identified this as **trying to prove a mathematically false statement**:
`IsLocalization.Away (κ_{D₀}(s_i)) (presheafValue D_i)` fails because the
completed rational localisation contains infinite convergent denominator tails
that no finite power of `s_i` clears. The reviewer's counterexample:
`A = ℚ_p⟨X⟩`, `D_i = R(X/1)` so `s_i = X` becomes a unit but
`A⟨T⟩/(XT - 1)` contains `∑_{n ≥ 0} p^n X^{-n}`, and multiplying by any `X^N`
leaves an infinite tail.

After that reframe, the project switched to the **Čech-acyclicity route** (Wedhorn
§8.3 + Appendix A.3) which is the current strategy. The Čech approach replaces
"localisation" by "flatness" of restriction maps (via Wedhorn 8.30/8.31), and
combines with Lemma 8.33 + Lemma 8.34 + Prop A.3 to get sheafiness.

---

## 3. Strategy

The current critical path (project artifacts call this **Block-A/B/C**) is:

1. **Block-A.** Lemma 8.33 — the 2-cover `𝒰_f = {R(f/1), R(1/f)}` is `𝒪_X`-acyclic.
   - Separation: Cor 8.32 ⟹ `ε` injective.
   - Gluing: the 5-lemma diagram chase from Wedhorn p. 83 (we'll quote it
     verbatim in §8.2).
   - Sub-inputs: Examples 6.38/6.39 (Laurent algebra identifications) + the
     row-1 surjectivity of `λ′` (Laurent decomposition equations).
2. **Block-B.** Lemma 8.34 — every rational cover generated by a finite ideal-
   generating set `T ⊆ A` is `𝒪_X`-acyclic. Four-part proof following Wedhorn
   p. 84:
   - (i) Every Laurent cover `𝒱 = 𝒰_{f₁} × ⋯ × 𝒰_{f_r}` is `𝒪_X`-acyclic
     (induction on `r`, base `r = 0` is the single-piece case, step is via Prop
     A.3(3) for cover product). Plus "the restriction of a Laurent cover to
     any rational subset is `𝒪_X`-acyclic".
   - (ii) For `T = (f₀,…,f_n)` ideal-spanning, there is a Laurent cover
     `(V_j)_{j ∈ J}` such that `𝒰|_{V_j}` is unit-generated. This uses Cor 7.32
     (dominating unit) + Wedhorn 7.40(6) (analytic ⇒ height ≤ 1) + the
     `s⁻¹·T` construction.
   - (iii) Every rational cover generated by units `f₀,…,f_n ∈ A^×` has a
     refinement by a Laurent cover (the ratios `f_i f_j^{-1}`).
   - (iv) Final assembly via Prop A.3(1) + Prop A.3(2).
3. **Block-C.** Project-side Prop A.3 bridges — translate Wedhorn's abstract
   Prop A.3(1)/(2)/(3) into the project's `RationalCovering` / `IsOXAcyclic`
   shape. This is the *cast plumbing* layer: dealing with `C'.base = C.base`
   equalities, `presheafValueCast` and friends.

At the top level: every open covering of `X` has a refinement by a rational cover
generated by an ideal-spanning Finset (Lemma 7.54). That refinement is
`𝒪_X`-acyclic by Lemma 8.34. Then Prop A.3(2) transfers acyclicity from the
refinement to the original cover. Finally Prop A.4 (in Wedhorn's Appendix)
gives sheafiness from acyclicity of every open cover.

The project has invested a long marathon (≈ 80 commits, 2026-05-28) into
closing the Block-C bridges (Prop A.3(1) and (2) for rational covers).
Both Prop A.3 parts are now **sorry-free in the project**, modulo two
structural hypotheses (`h_V_refines_C`, `h_C'_covers_each_D`) that we found
were missing from the original sketches and added during the marathon. These
hypotheses are naturally available at consumers.

What remains (24 sorries on this file) splits into five buckets:

- **Bucket B1** — B2-class signature defects (this brief's §9 Q1). Three lemmas
  are mathematically false as stated and need either a hypothesis addition or
  consumer refactor.
- **Bucket B2** — small base cases (single-piece-cover `R({1}/1)` separation
  and gluing): ~50 LOC, mechanical, not interesting.
- **Bucket B3** — cover-each companion lemmas for σ-walk arguments (Wedhorn
  8.34 (ii)/(iii) plus the strengthened Lemma 7.54).
- **Bucket B4** — substantive Wedhorn-text leaves (Wedhorn 6.18, 7.40(6), the
  evalHom-continuity Examples 6.38/6.39 side, and the **5-lemma body** for
  Lemma 8.33 — this brief's §9 Q2).
- **Bucket B5** — combinatorial constructions (Laurent decomposition, σ-walk
  bodies). Mechanical but lengthy.

Buckets B1 and B4's 5-lemma are the two we want reviewer input on.

---

## 4. Definitions

### 4.1 Rational covering predicates

For a `RationalCovering C` of `A` with base `D := C.base` (so `C.covers` is a
finite set of rational loc data, each refining `D`):

- **C is generated by `T ⊆ A`** (Wedhorn p. 83's phrasing, our `IsGeneratedBy T`):
  - `T · A = A` (the unit-ideal condition), and
  - there is a bijection `φ : T ≃ C.covers` such that for each `t ∈ T`, the
    piece `φ(t)` has `T`-set equal to `T` and `s`-element equal to `t`.

  Concretely the pieces are `R(T/t₁), R(T/t₂), …, R(T/t_n)` for the `n` elements
  of `T`. The bijection is part of the predicate; the same `T` appears in every
  piece's `T`-set.

- **C is unit-generated** (our `IsUnitGenerated`): for every piece `D' ∈ C.covers`
  and every `t ∈ D'.T`, the canonical image `canonicalMap_{C.base}(t)` is a unit
  in `𝒪_X(C.base)`. This is the weaker condition Wedhorn uses in 8.34 (ii)
  (Laurent `(V_j)` chosen so that "𝒰|_{V_j} is unit-generated" in this sense).

- **C is a Laurent cover by `fs : List A`** (our `IsLaurentCover fs`): C is
  generated (in the previous sense) by the Finset of products of subsets of
  `fs`. Wedhorn p. 84: `𝒱 := 𝒰_{f₁} × ⋯ × 𝒰_{f_r}` is the rational cover of `X`
  generated by `T = {∏_{j ∈ J} f_j : J ⊆ {1,…,r}}`. The pieces correspond
  bijectively to the `2^r` subsets `J`.

- **C is `𝒪_X`-acyclic** (our `IsOXAcyclic`): the 0-cohomology form of the
  Čech complex described in §2.1. Two fields: `separation` and `gluing`.

### 4.2 The `restrictToPiece` construction

Given a `RationalCovering C'` of some base and a sub-rational-subset `D ⊆ C'.base`
such that the rational opens of `C'.covers` cover `D`, we define

`C'.restrictToPiece D := { base := D; covers := C'.covers.filter (R(D'.T/D'.s) ⊆ R(D.T/D.s)) }`

This *keeps only* those `C'`-pieces that fit inside `D`; the kept pieces are
unchanged. In particular each kept piece is **literally a `C'`-piece** (same
`T`-set, same `s`-element). The bijection-with-`T` of `IsGeneratedBy T` survives
this filter only if every `C'`-piece is kept, i.e. only if `R(C'.base.T/C'.base.s)`
sits inside `R(D.T/D.s)`. In our cases we always have `D ⊆ C'.base`, so the
filter is non-trivial and pieces are lost.

### 4.3 The presheaf value and cast helpers

`presheafValue D := UniformSpace.Completion (Localization.Away D.s)` with the
topology making `D.T / D.s` power-bounded. For `D ⊆ D'` we have a
`restrictionMap D' D : presheafValue D' → presheafValue D` (a continuous ring
hom; in the project it's bundled both as `restrictionMap` and `restrictionMapHom`,
definitionally equal). For `D₁ = D₂` as `RationalLocData` there is a cast
`presheafValueCast (h : D₁ = D₂) : presheafValue D₁ ≃+* presheafValue D₂` that
the marathon added explicitly to avoid `Eq.rec` motive issues.

---

## 5. Established results (what is sorry-free in the project)

We list the load-bearing results that are *fully proved* in the file
`WedhornCechAcyclicity.lean` (≈ 2500 LOC, 24 sorries). Mathlib-style names
preserved as structural labels where mathematically meaningful.

### 5.1 Cor 8.32 (faithful flatness ⟹ injectivity)

For a 2-cover `{D₁, D₂}` of `D₀`, the product map `𝒪_X(D₀) → 𝒪_X(D₁) × 𝒪_X(D₂)`
is injective. The project proves this via an existing axiom-clean
`cor_8_32_clean_proof` (the faithful-flatness piece comes from Wedhorn 8.30/8.31).

### 5.2 Lemma 8.33 separation

For the 2-cover `𝒰_f = {R(f/1), R(1/f)}` of `D₀`, the separation field of
`IsOXAcyclic` holds. Direct corollary of 5.1.

### 5.3 Examples 6.38 and 6.39 — column exactness

Five sub-lemmas covering both branches:

> 𝒪_X(R(f/1)) ≅ A⟨ζ⟩/(f − ζ),
> 𝒪_X(R(1/f)) ≅ A⟨η⟩/(1 − fη),
> 𝒪_X(R(f/1) ∩ R(1/f)) ≅ A⟨ζ, ζ⁻¹⟩/(f − ζ).

(Plus matching ring-iso witnesses extracted via `Nonempty`.) The completeness
side condition is `inferInstance`. The noetherian-pair-subring side condition
(Wedhorn 6.18) and two `evalHom` continuity side conditions are the **only
remaining gaps** on this chain (see §8 below — sorries 1, 2, 5 in the inventory).

### 5.4 Prop A.3(2) project bridge — gluing direction

Statement: given `C, C' : RationalCovering A` with `C'.base = C.base`, every
`C'`-piece refining some `C`-piece, `C'` acyclic, plus the *double-restriction
acyclicity* and *covers-each-D* hypotheses (each `D ∈ C.covers` is covered by
`C'`-pieces refining into it), conclude `C`-gluing.

This is the most substantive Block-C landing (2026-05-28). The proof
constructs `E_D := C'.restrictToPiece D` for each `D ∈ C.covers`, uses
`E_D.IsOXAcyclic` from the double-restriction hypothesis, builds a compatible
family on `C'` by choosing for each `D' ∈ C'.covers` a refining `D ∈ C.covers`
via `Classical.choose` on the refinement hypothesis and pulling back `f D`, then
applies `C'.gluing` to get a section `x'`, casts through `presheafValueCast` to
get `x ∈ presheafValue C.base`, and verifies `x|_D = f D` for each `D` via
`E_D.separation` and `restrictionMap_comp`.

### 5.5 Prop A.3(1) project bridge — gluing direction

Analogous statement for refining `V → C` (V-pieces refine C-pieces) instead of
the `C' → C` direction of A.3(2). Closed 2026-05-28 by adding a hypothesis
`h_V_refines_C` and extracting a helper lemma `inner_identity_generic` that
proves `yV V_j = restrictionMap D_i V_j (f D_i)` whenever `V_j ⊆ D_i` and `D_i`
is the `C`-piece chosen for `V_j` by `h_V_refines_C`.

### 5.6 Lemma 8.34 part (i) base case

Extracts the single-piece structure from `V.IsLaurentCover []`: the empty
Laurent has its generating Finset `{1}`, so `V.covers = {D₀}` with
`D₀.T = {1}`, `D₀.s = 1`.

### 5.7 Lemma 8.34 part (iv) compositions

The V-restriction acyclicity (V|U for the Laurent V is acyclic on each
piece U ∈ C.covers, by part-(i) restriction corollary applied to V|_U) is
sorry-free. The companion `C_restr_acyclic` is also closed modulo the
part-(iii) body sorry.

### 5.8 Cor 7.32

The composition is sorry-free; three leaves remain open (see §8 inventory).

### 5.9 Top-level theorem skeleton

The headline `isSheafy_ofStronglyNoetherianTate_clean` compiles. Its body
composes `every_rational_cover_is_OXAcyclic` (sorries modulo Bucket B4 + Bucket
B1) with the `productRestrictionSub_isInducing_tate` piece (sorry-free, in a
separate file).

---

## 6. In progress

There are 24 sorries on the active file `WedhornCechAcyclicity.lean`.
Grouped as in §3:

**Bucket B1 — B2 signature defects (3 sorries, this brief's Q1).**

- `restricted_cover_inherits_IsUnitGenerated` — given `C'` generated by `T`,
  `D : RationalLocData`, `E` a `RationalCovering` of `D` with each piece
  refining some `C'`-piece, conclude `E.IsUnitGenerated`. The hypotheses are
  insufficient: the conclusion's universally quantified `t ∈ E'.T` has no
  structural relationship to `T`, and no ring-hom transfers `IsUnit
  canonicalMap_{C'.base} t` to `IsUnit canonicalMap_D t` without
  `R(D.T/D.s) ⊆ R(C'.base.T/C'.base.s)`.
- `restricted_cover_inherits_IsGeneratedBy` — same as above plus a worse
  bijection-failure issue: `E.covers ↔ T` via the filter `restrictToPiece`
  can have strictly fewer pieces than `T` whenever `D ⊆ C'.base` is proper
  (which is the only case used).
- `laurent_restriction_isLaurent` — claims `V_restrict.IsLaurentCover fs` for
  the same `fs` whose images we'd actually want to use. Wedhorn p. 84 says
  the restriction `V|_U` is the Laurent cover generated by *`f_{i|U}`* (the
  images in `𝒪_X(U)`), not by the original `f_i ∈ A`. The project's
  `IsLaurentCover fs` predicate ranges `fs : List A`, so using the same `fs`
  is a mismatch.

These three drive **Q1** in §9.

**Bucket B2 — single-piece base case (2 sorries).**

`isOXAcyclic_of_single_unit_piece_separation` and `_gluing` —
`V` has cover `{D₀}` with `D₀.T = {1}`, `D₀.s = 1`. The pieces' rationalOpen
equals `V.base`'s rationalOpen, so the restriction map is the identity
(through a ring iso). Mechanical, ~25 LOC each.

**Bucket B3 — cover-each companions (4 sorries).**

These were extracted during the 2026-05-28 marathon as sub-decompositions of
σ-walk arguments:

- `ratio_laurent_covers_each_unit_gen_piece` — for each `D ∈ C.covers` of a
  unit-generated cover, every `v ∈ R(D.T/D.s)` is in some ratio-Laurent piece
  `V' ⊆ V` with `V' ⊆ D`.
- `laurent_cover_refines_idealgen_cover` — the Laurent cover from a dominating
  unit refines the ideal-generated cover.
- `laurent_cover_covers_each_idealgen_piece` — covers-each direction for the
  above.
- `ideal_gen_refinement_covers_each_piece` — Lemma 7.54-strengthened: for each
  `D ∈ C.covers` and `v ∈ R(D.T/D.s)`, there is a refinement piece `D'` with
  `v ∈ R(D'.T/D'.s) ⊆ R(D.T/D.s)`.

Each is provable from the σ-walk infrastructure once the corresponding base
σ-walk lemma lands.

**Bucket B4 — substantive Wedhorn-text leaves (7 sorries).**

- `example_638_plus_side_noeth_pairSubring` — Wedhorn 6.18 (strongly noeth Tate
  ⇒ noeth pair-subring of Tate algebra). Substantive.
- `example_638_plus_side_cont_evalHom` and `_minus_side_cont_underlying_evalHom`
  — continuity of the evaluation hom `A⟨ζ⟩ → 𝒪_X(R(f/1))` mapping `ζ ↦
  canonicalMap f`. Should reduce to the project's `evalHomBounded` machinery
  plus quotient-topology lifting.
- **`wedhorn_lemma_833_gluing_as_field`** — the 5-lemma diagram chase body
  (Wedhorn p. 83). This is **Q2**.
- `exists_principal_pair_with_A₀_subset_Aplus_and_pseudouniformizer` —
  Wedhorn 6.14 + Remark 7.17 (smallest A₀ inside A⁺ has a topologically nilpotent
  unit generator). Substantive but textbook.
- `mulArchimedean_valueGroup_of_stronglyNoetherianTate` — Wedhorn 7.40(6)
  (analytic point of a strongly-noeth Tate ring has height-1 value group).
  Substantive (~150 LOC est.) but textbook.
- `rationalCovering_from_idealGenSet` — Wedhorn 7.54 (every ideal-spanning
  `T ⊆ A` produces a rational cover `(R(T/t))_{t∈T}`). Mostly combinatorial.

**Bucket B5 — combinatorial constructions (8 sorries).**

`laurent_cons_decomp_as_product` (Laurent product decomposition), `laurent_cover_from_dominating_unit`,
`index_selection_on_laurent_piece` (σ-walk dominant), `canonical_unit_of_pointwise_lower_bound`,
`unit_gen_restriction_of_dominating_laurent`, `ratio_laurent_cover_of_units`,
`ratio_laurent_refines_unit_gen`, plus `propA3_part3_bridge_for_laurent_product`.
Each is mechanical Wedhorn-style σ-walk or Laurent-product manipulation.

---

## 7. Targets (skipped — out of scope of this brief)

The full Theorem 8.28(b), and downstream sheafiness of adic spectra of more
general Tate algebras (Cor 8.35). These are not in scope here; they are
unblocked once the 24 sorries above are discharged.

---

## 8. Where we're stuck

We surface **two specific stuck points** for reviewer input. The rest of the
project's open work (Buckets B2/B3/B5 and the non-5-lemma parts of B4) is
unstuck — those are mechanical or textbook proofs and don't need external
guidance.

### 8.1 Stuck point: signature defects in the restriction-inherit lemmas

**Setting.** The Wedhorn 8.34 (iv) final assembly needs, for each `D` in some
"big" rational cover `C` of `X` and each `D'`-refinement `C' → C`, to transfer
properties of `C'` to a restricted-cover `E` of `D`. The natural construction
is `E := C'.restrictToPiece D` — filter `C'.covers` to those pieces inside `D`.

The two lemmas the project needs are:

> **Lemma (project, false as stated).** *Let `C'` be a rational covering generated
> by `T ⊆ A`. Let `D ∈ C.covers`. Let `E` be a rational covering of `D` such that
> every `E`-piece refines some `C'`-piece. Then `E.IsUnitGenerated`.*

and the parallel claim with conclusion `E.IsGeneratedBy T`.

**Why they're false as stated.** The `IsUnitGenerated` conclusion is
`∀ E' ∈ E.covers, ∀ t ∈ E'.T, IsUnit (E.base.canonicalMap t)`. The given
hypotheses provide `IsUnit (C'.base.canonicalMap t)` for `t ∈ T = D'.T`
(some `D'`-piece in `C'`). Two structural facts are missing:

(a) **Refinement of base.** Without `R(D.T/D.s) ⊆ R(C'.base.T/C'.base.s)`, there
is no ring hom `𝒪_X(C'.base) → 𝒪_X(D)` factoring `canonicalMap` to transfer
`IsUnit`. The image of a unit in a ring hom is a unit, so this is the
load-bearing piece.

(b) **Generator transfer.** For arbitrary `t ∈ E'.T`, `t` need not be in `T`.
The refinement hypothesis only says `R(E'.T/E'.s) ⊆ R(D'.T/D'.s)`, which does
not imply `E'.T ⊆ T` or any other concrete equality of generator sets.

For the `IsGeneratedBy T` variant, the bijection `E.covers ↔ T` of the
predicate is additionally violated by the filter construction whenever some
`C'`-piece does not refine into `D` — the filtered `E.covers` has strictly
fewer pieces than `|T|`.

**What the consumer naturally has.** At every concrete callsite the project
actually uses, the missing structural facts are available:

- (a) `D ∈ C.covers` is given. The project's `RationalCovering` carries
  `C.hsubset : ∀ D ∈ C.covers, R(D.T/D.s) ⊆ R(C.base.T/C.base.s)`. Combined
  with the side hypothesis `C'.base = C.base` (used elsewhere on this chain),
  this gives `R(D.T/D.s) ⊆ R(C'.base.T/C'.base.s)`.
- (b) The natural `E` is `C'.restrictToPiece D`, which guarantees every
  `E`-piece is **literally** a `C'`-piece (same `T`-set, same `s`). So
  `E'.T = D'.T = T` (where `D' = E'`).

So the two hypotheses (a) and (b) **are naturally present** at the call site
but were not threaded through this intermediate lemma's signature.

**What we tried.** During the audit we identified three candidate fixes:

1. **Add the missing hypotheses to the lemma's signature** and propagate
   through the consumer chain (`double_restriction_acyclicity` →
   `wedhorn_lemma_834_E_acyclic` → `every_rational_cover_is_OXAcyclic`). This
   is permitted by the project's binding rule ("the result is genuinely
   mathematically false without the addition"), and touches ~3-5 lemmas. The
   `IsGeneratedBy T` variant is harder to save this way because of the
   bijection issue.
2. **Collapse the intermediate** — instead of going through
   `restricted_cover_inherits_IsUnitGenerated`, route the consumer directly
   through `propA3_part2_project_gluing` applied to `E` as a refinement of the
   trivial 1-cover at `D`. This avoids stating an "inherit" predicate at all.
3. **Reformulate via canonical images** — change `IsUnitGenerated` to say
   "every `t ∈ E'.T` is the canonical image of some `s ∈ A` with
   `IsUnit (E.base.canonicalMap s)`". This preserves the predicate but shifts
   the bookkeeping to the construction.

**Related defect on the Laurent side.** `laurent_restriction_isLaurent` has
the same shape of issue: claims `V_restrict.IsLaurentCover fs` for the same
`fs`, but Wedhorn explicitly says `V|U` is the Laurent cover generated by
`f_{1|U}, ..., f_{r|U}` (the *images* in `𝒪_X(U)`). The project's predicate
ranges `fs : List A`, not `List 𝒪_X(U)`, so the same-`fs` statement is
genuinely false for the `restrictToPiece` consumer that filters and loses
pieces. The fix here is more invasive: either restate the predicate to track
image-lists, or refactor the consumer
`wedhorn_lemma_834_part_i_laurent_restriction_acyclic` to use
`propA3_part2_project_gluing` directly on `V → V_restrict` (V is acyclic by
part (i), V_restrict refines V on the base D, so propA3_part2 transfers
acyclicity).

### 8.2 Stuck point: the 5-lemma diagram chase body

**Setting.** Wedhorn's proof of Lemma 8.33 produces the gluing direction
(exactness at the middle of the augmented Čech complex) by a 5-lemma diagram
chase. Verbatim from Wedhorn p. 83-84:

> *Proof of Lemma 8.33.* We may assume that A is complete (to simplify the
> notation). We have already seen that ε is injective (Corollary 8.32).
> Moreover, by Examples 6.38 and 6.39 we have
>
> $\mathcal{O}_X(U_1) = A\langle\zeta\rangle/(f - \zeta)$,
> $\mathcal{O}_X(U_2) = A\langle\eta\rangle/(1 - f\eta)$,
> $\mathcal{O}_X(U_1 \cap U_2) = A\langle\zeta, \eta\rangle/(f - \zeta, 1 - f\eta) = A\langle\zeta, \eta\rangle/(f - \zeta, 1 - \zeta\eta) = A\langle\zeta, \zeta^{-1}\rangle/(f - \zeta)$.
>
> Consider the following commutative diagram
>
> ```
>                                 0                                    0
>                                 ↓                                    ↓
>             (f - ζ)A⟨ζ⟩ × (1 - fη)A⟨η⟩  →^{λ'}  (f - ζ)A⟨ζ, ζ⁻¹⟩  →  0
>                                 ↓                                    ↓
>             A   →^ι    A⟨ζ⟩ × A⟨η⟩      →^λ    A⟨ζ, ζ⁻¹⟩            → 0
>             ‖                   ↓                                    ↓
>     0  →    A   →^ε    𝒪_X(U_1) × 𝒪_X(U_2)  →^δ  𝒪_X(U_1 ∩ U_2)    → 0
>                                 ↓                                    ↓
>                                 0                                    0
> ```
>
> Here `ι` is the canonical injection, `λ` is the map
> `g((ζ), h(η)) ↦ g(ζ) - h(ζ⁻¹)`, and `λ'` is induced by `λ`. The columns are
> exact by (8.2.1). A diagram chase shows that if the first and second row are
> exact, then the third row is exact (note that we know already the injectivity
> of `ε`).
>
> The equations
>
> $A\langle\zeta, \zeta^{-1}\rangle = A\langle\zeta\rangle + \zeta^{-1} A\langle\zeta^{-1}\rangle$,
> $(f - \zeta) A\langle\zeta, \zeta^{-1}\rangle = (f - \zeta) A\langle\zeta\rangle + (1 - f\zeta^{-1}) A\langle\zeta^{-1}\rangle$
>
> show the surjectivity of `λ` and `λ'` (and in particular the exactness of the
> first row). Finally, the equality
>
> $0 = \lambda(\sum_{k \geq 0} a_k \zeta^k, \sum_{k \geq 0} b_k \eta^k) = \sum_{k \geq 0} a_k \zeta^k - \sum_{k \geq 0} b_k \zeta^{-k}$
>
> is equivalent to `a_k = b_k = 0` for `k > 0` and `a_0 = b_0`. Thus
> `im(ι) = ker(λ)`. ∎

**What we need to produce in Lean.** The project's `wedhorn_lemma_833_gluing_as_field`
asks for the following: given a compatible family `g₁ ∈ 𝒪_X(R(f/1))`, `g₂ ∈ 𝒪_X(R(1/f))`
on the 2-cover `𝒰_f = {R(f/1), R(1/f)}` of `D₀`, produce `x ∈ presheafValue D₀`
such that `x|R(f/1) = g₁` and `x|R(1/f) = g₂`.

Mathlib has the Examples 6.38/6.39 column isomorphisms already (sorry-free in
the project) so the columns of the diagram are available as concrete ring
equivs. What we need is:

(i) **Row 1 surjectivity** (`λ′` surjective onto `(f - ζ)A⟨ζ, ζ⁻¹⟩`). Wedhorn
proves this from the equation `(f - ζ)A⟨ζ, ζ⁻¹⟩ = (f - ζ)A⟨ζ⟩ + (1 - fζ⁻¹)A⟨ζ⁻¹⟩`,
which in turn rests on the Laurent decomposition `A⟨ζ, ζ⁻¹⟩ = A⟨ζ⟩ + ζ⁻¹ A⟨ζ⁻¹⟩`.

(ii) **Row 2 kernel computation** (`ker(λ) = im(ι) = A`, with `λ(g(ζ), h(η)) = g(ζ) - h(ζ⁻¹)`).
Wedhorn does this by direct computation on power-series coefficients: setting
`λ(Σ a_k ζ^k, Σ b_k η^k) = Σ a_k ζ^k - Σ b_k ζ^{-k} = 0` forces `a_k = b_k = 0`
for `k ≥ 1` and `a_0 = b_0`, so the kernel is the diagonal `A`.

(iii) **Diagram chase.** Given the columns + rows 1, 2 exact and `ε` injective,
diagram-chase to row 3 exactness at the middle. Standard 5-lemma argument
but Wedhorn's proof phrases it as "rows 1 and 2 exact ⟹ row 3 exact" rather
than as a 5-lemma application.

**What mathlib offers (best of our knowledge).** Mathlib has:

- `Mathlib.Algebra.Homology.ShortComplex.FiveLemma` — the categorical
  Five-Lemma for `ShortComplex` in an abelian category. The presheaf-value
  rings live in `CommRingCat` (not abelian; abelian categories are R-Mod
  for fixed R), so this would require landing in `ModuleCat A` or
  `AddCommGroupCat` and re-bundling.
- `RingHom.injective_iff_ker_eq_bot`, `RingHom.surjective`, etc. — basic
  surjectivity / injectivity lemmas.
- `Polynomial.coeff_zero_eq_zero_iff` and friends for power-series
  coefficient extraction in `MvPowerSeries`, `PowerSeries`. The Laurent
  ring `A⟨ζ, ζ⁻¹⟩` is `LaurentPolynomial A`-completion-style; the project's
  version is the Tate-algebra-localised-at-ζ `A⟨ζ⟩[ζ⁻¹]^∧`.
- `Localization.away_iff` / `IsLocalization.Away.mk'_one_eq` for the
  ζ⁻¹-adjunction side.

What is **probably not** in mathlib:

- The Laurent decomposition `A⟨ζ, ζ⁻¹⟩ = A⟨ζ⟩ + ζ⁻¹ A⟨ζ⁻¹⟩` as a direct
  sum of A-modules. The closest analogues are decompositions of
  `MvPowerSeries` into positive / negative parts, which need adaptation.
- The ideal decomposition `(f - ζ) A⟨ζ, ζ⁻¹⟩ = (f - ζ) A⟨ζ⟩ + (1 - fζ⁻¹) A⟨ζ⁻¹⟩`.
- The specific `ker(λ) = A` computation via power-series coefficient matching.

**What we have so far on this sorry.** Nothing. The body is `sorry` with the
in-line note `"The 5-lemma argument from Wedhorn p. 84 lifts a compatible pair
(g(U₁), g(U₂)) on (R(f/1), R(1/f)) to a section on X = D₀."`. The project
previously had three `True := by trivial` placeholder lemmas for the row-1
surjectivity, row-2 kernel, and 5-lemma composition; these were removed in the
2026-05-28 cleanup at the user's request because they were not actual
sub-decompositions.

**What we'd like to know.** See Q2 in §9.

---

## 9. Open mathematical questions for the reviewer

### Q1. Signature-defect resolution for the restriction-inherit chain

We have three lemmas that are mathematically false as stated (§8.1):
`restricted_cover_inherits_IsUnitGenerated`,
`restricted_cover_inherits_IsGeneratedBy`,
`laurent_restriction_isLaurent`. The needed structural facts (`E.base ⊆ C'.base`,
`E'.T related to T`, image-tracking for the Laurent generators) are all
naturally available at the call sites but were not threaded through.

(a) **Is the right move (i) adding the missing hypotheses to these
intermediates and propagating to consumers, (ii) collapsing the intermediates
and routing consumers directly through `propA3_part2_project_gluing` applied to
the refinement, or (iii) refactoring the upstream predicates
(`IsLaurentCover`, `IsGeneratedBy`, `IsUnitGenerated`) to track images in
`𝒪_X(base)` rather than elements of `A`?** Each has costs:

  - (i) keeps the predicate stable but adds ~3-5 hypothesis lines to each
    intermediate and ~10 lines per consumer.
  - (ii) deletes ~80 LOC of intermediate sub-lemmas; the consumer code becomes
    one more `propA3_part2` invocation. Risk: the per-piece "double-restriction
    acyclicity" hypothesis of `propA3_part2` may require its own restating
    again.
  - (iii) is the most Wedhorn-faithful (Wedhorn p. 84 explicitly says "the
    Laurent cover generated by `f_{1|U}, ..., f_{r|U}`"), but invasive: every
    `IsLaurentCover` consumer needs to learn about the image translation.

We expect (i) is the right answer for `restricted_cover_inherits_IsUnitGenerated`
and (ii) for `restricted_cover_inherits_IsGeneratedBy` (the bijection issue
isn't fixable by hypothesis), and (iii) for `laurent_restriction_isLaurent`
(the image-vs-original mismatch is exactly what Wedhorn says). But (iii)'s
invasiveness worries us — it touches every place the project uses the Laurent
predicate, which is most of Block-B.

**Specific ask.** Has Wedhorn (or some other reference) given a cleaner
formulation that side-steps the same-`fs` issue for the restricted cover?
The phrasing "Laurent cover generated by `f_{i|U}`" reads like a different
object — would you state the project's `IsLaurentCover` to range over
generators in `𝒪_X(base)` rather than in `A`, and accept the cascade?

(b) **For the `restricted_cover_inherits_IsGeneratedBy` bijection.** Wedhorn's
`IsGeneratedBy` predicate (p. 83) seems to require the pieces correspond
bijectively to `T`. If `E` is a restriction that *loses* some pieces, the
correct statement is "E is generated by some subset `T' ⊆ T`" rather than
"E is generated by `T`". Is the standard formulation in the literature using
a sub-Finset, or do textbooks finesse this in a way we're missing?

### Q2. 5-lemma diagram chase for Wedhorn 8.33

The body of `wedhorn_lemma_833_gluing_as_field` needs to produce the row-3
exactness at the middle for the diagram in §8.2.

**What's available in mathlib (we believe).** `Mathlib.Algebra.Homology.ShortComplex.FiveLemma`
for abelian categories; `RingHom.ker`, `Ideal.span` and quotient infrastructure;
`MvPowerSeries.coeff` for coefficient extraction; `IsLocalization.Away` for
the ζ⁻¹-adjunction.

**What seems missing.**

  - Laurent decomposition `A⟨ζ, ζ⁻¹⟩ = A⟨ζ⟩ + ζ⁻¹ A⟨ζ⁻¹⟩` (as A-modules / as ideals).
  - The corresponding ideal-level decomposition for `(f - ζ) A⟨ζ, ζ⁻¹⟩`.
  - The categorical 5-lemma in `CommRingCat` form (or the willingness to lift
    everything to `ModuleCat A`).

**Specific asks.**

  (a) **Is the categorical 5-lemma in mathlib usable here, or should we do
  the diagram chase by hand on `CommRingCat`?** Wedhorn phrases the chase
  informally ("if rows 1 and 2 exact, then row 3 exact, knowing `ε` is
  injective"). For a hand chase we'd reformulate as: given `(g₁, g₂) ∈ row 3
  middle` with `δ(g₁, g₂) = 0`, lift to `(g₁', g₂') ∈ row 2 middle`, compute
  `λ(g₁', g₂') ∈ (f - ζ) A⟨ζ, ζ⁻¹⟩` (via the column kernel), get a row-1
  preimage `(γ₁, γ₂)`, subtract to land in `ker(λ) = A` via row-2 exactness,
  and that `A`-element is `x` with `ε(x) = (g₁, g₂)`. Either route eventually
  needs the Laurent decomposition.

  (b) **What's the cleanest formulation of the Laurent decomposition
  `A⟨ζ, ζ⁻¹⟩ = A⟨ζ⟩ + ζ⁻¹ A⟨ζ⁻¹⟩` in Lean / Mathlib?** Options we see:

  - Direct: view `A⟨ζ, ζ⁻¹⟩` as a `LaurentPolynomial`-completion, decompose
    into non-negative and strictly-negative parts.
  - Via `IsLocalization.Away`: `A⟨ζ, ζ⁻¹⟩ = A⟨ζ⟩[ζ⁻¹]^∧`; decompose along
    the powers of `ζ⁻¹`.
  - Via the `MvPowerSeries` infrastructure with index set `ℤ` rather than
    `ℕ`, and Wedhorn-style strict-bound on negative-degree coefficients.

  (c) **The `ker(λ) = A` computation.** Wedhorn computes this by coefficient
  matching:

  > `λ(Σ a_k ζ^k, Σ b_k η^k) = Σ a_k ζ^k - Σ b_k ζ^{-k}`,
  > so vanishing forces `a_k = b_k = 0` for `k ≥ 1` and `a_0 = b_0`.

  Is the right formalisation route `MvPowerSeries.coeff_injective` plus the
  coefficient comparison, or do you see a more abstract route (e.g., via the
  associated `Pi.algebra` decomposition `A⟨ζ⟩ × A⟨η⟩ ≃ A ⊕ A⟨ζ⟩_{>0} ⊕
  A⟨η⟩_{>0}` and then directly extracting the diagonal)? The `Pi.algebra`
  route would side-step the coefficient comparison entirely.

  (d) **Alternative routes the project should consider.** Are there any
  recent treatments of Lemma 8.33 (or its analogue in rigid-analytic geometry
  via Tate's acyclicity) that bypass the diagram chase entirely? We are aware
  of Tate's original acyclicity theorem and BGR's treatment, but those go via
  Banach-OMT which we ruled out earlier. Is there a Mittag-Leffler-style or
  Čech-derived-functor argument that lands in our setting more cleanly?

  (e) **Sanity check.** The project previously had three `True := by trivial`
  placeholder lemmas for the row-1, row-2, and 5-lemma sub-pieces of this
  argument. We removed them per a binding rule ("no placeholders") and the
  body is now a single `sorry`. Is the right granularity for sub-decomposition
  (i) one sub-lemma per row + one for the chase, (ii) one sub-lemma per
  Wedhorn equation (Laurent decomp, ideal decomp, kernel computation, chase),
  or (iii) just inline everything into the body? We tentatively prefer (ii)
  but want to confirm.

---

## 10. Auxiliary technical results (appendix)

For reference, here are the existing project lemmas that come up in the
discussion above. Statements only — no proofs needed.

**Lemma (`RationalCovering.restrictToPiece`).** *Given `C' : RationalCovering A`
and a rational subset `D` such that the rational opens of `C'.covers` cover `D`,
the assignment*

`C'.restrictToPiece D := { base := D; covers := C'.covers.filter (·.rationalOpen ⊆ D.rationalOpen) }`

*is a `RationalCovering` of `D`. Pieces of `C'.restrictToPiece D` are pieces of
`C'` unchanged in `T` and `s`.*

**Lemma (`presheafValueCast`).** *For `D₁, D₂ : RationalLocData A` and
`h : D₁ = D₂`, there is a ring isomorphism `presheafValue D₁ ≃+* presheafValue D₂`
that intertwines `canonicalMap` and `restrictionMap`.*

**Lemma (`restrictionMap_comp`).** *For nested rational subsets `D₀ ⊇ D₁ ⊇ D₂`,
`restrictionMap D₁ D₂ ∘ restrictionMap D₀ D₁ = restrictionMap D₀ D₂`.*

**Lemma (`canonicalMap_at_T`).** *For `D : RationalLocData A` and `t ∈ D.T`,
`canonicalMap_D t / canonicalMap_D D.s` is well-defined and `canonicalMap_D D.s`
is a unit in `presheafValue D`.*

**Lemma (Examples 6.38 plus).** *For a Tate ring `A` with principal pair
`(A₀, (s))` and `f ∈ A`, there is a ring isomorphism
`A⟨ζ⟩/(f - ζ) ≃+* 𝒪_X(R(f/1))` sending `ζ ↦ canonicalMap f`.*

(The minus branch is parallel with `A⟨η⟩/(1 - fη)` and `R(1/f)`.)

---

## 11. Document metadata

- Project name: Adic spaces (Lean 4 formalisation of Wedhorn's *Adic Spaces*)
- Brief generated: 2026-05-28
- Length: approx. 11 pages
- Build status at time of writing: `lake build` clean (warnings only).
  `WedhornCechAcyclicity.lean` has 24 substantive `sorry` declarations.
- Recent commit context: 80 commits since 2026-05-28 in a marathon session;
  Wedhorn Prop A.3 chain (parts 1+2 separation+gluing) landed sorry-free.
  Most recent activity is documentation and cleanup; no new substantive
  proofs since `wedhorn_lemma_834_propA3_part1_gluing` at commit `d29fdee`.
- Scope of brief: narrow — only the two questions in §9.

---

*End of brief.*
