# ChatGPT Pro Packet — T-NULL-PER-E C1: Zavyalov §2.3 candidate-family construction

## 0. Purpose

We are formalising Wedhorn's *Adic Spaces*, Theorem 8.28(b) (**Tate
acyclicity**) in Lean 4 + Mathlib. The final assembly step relies on
Wedhorn's §8.34 (Hübner Lemma 3.8) "geometric reduction": any rational
cover can be refined to a **standard rational cover** whose pieces are
plus-pieces over the same denominator. The **single remaining gap** is
the explicit construction of the refining elements ("C1"). This packet
asks for the precise algebraic formula — we do **not** want a Lean
proof back, we want the Zavyalov §2.3 ratio-clearing argument stated
cleanly enough to translate.

Everything else on the T-NULL-PER-E path is landed (C2 quasi-compactness
of rational opens via Bool cylinders; C3 span-top via Prop 7.14; the
per-D assembly). C1 is the single unresolved piece.

## 1. Final Lean goal

The downstream consumer is `tateAcyclicity_Part2_via_hZavyalov_per_E_direct`
in `GeometricReduction.lean`. It takes the following existential
hypothesis on the rational covering `C : RationalCovering A`:

```lean
-- hZavyalov_per_E : the strengthened Nullstellensatz refinement
∃ S : Finset A,
    refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S
```

Unpacking the three predicates:

```lean
def refines_cover_per_E (C : RationalCovering A) (S : Finset A) : Prop :=
  ∀ E ∈ C.covers, ∀ v ∈ rationalOpen E.T E.s,
    ∃ f ∈ S,
      v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen E.T E.s

def refines_contain (C : RationalCovering A) (S : Finset A) : Prop :=
  ∀ f ∈ S, ∃ D ∈ C.covers,
    rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s

def refines_span_top (S : Finset A) : Prop :=
  Ideal.span (S : Set A) = ⊤
```

Here `RationalCovering A` is Wedhorn's Definition 8.1:
```lean
structure RationalCovering (A : Type*) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [PlusSubring A] where
  base : RationalLocData A
  covers : Finset (RationalLocData A)
  hsubset : ∀ D ∈ covers, rationalOpen D.T D.s ⊆ rationalOpen base.T base.s
  hcover  : ∀ v ∈ rationalOpen base.T base.s,
              ∃ D ∈ covers, v ∈ rationalOpen D.T D.s
```
and `RationalLocData A` packages a "rational localisation datum" with a
pair of definition `P`, a finite set `T : Finset A`, an element `s : A`,
and the `hopen` condition controlling the localisation topology.

`rationalOpen T s = { v ∈ Spa A A⁺ | (∀ t ∈ T, v.vle t s) ∧ ¬ v.vle s 0 }`
is Wedhorn's `R(T, s) = Spa(A, A⁺)(T/s)` — the adic rational subset.

## 2. What is already landed

### 2.1 Assembly infrastructure (in `StandardCover.lean`, all axiom-clean)

`exists_refines_cover_per_E_of_per_D_construction` — **reduces the goal
to per-piece data**. Given for each `D ∈ C.covers` a finite subfamily
`mk_S_D D : Finset A` with:

- `h_in_D  : ∀ D ∈ C.covers, ∀ f ∈ mk_S_D D,
              rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s`
- `h_cover_D : ∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
                 ∃ f ∈ mk_S_D D, v ∈ rationalOpen (insert f C.base.T) C.base.s`
- `h_span : Ideal.span ((C.covers.biUnion mk_S_D : Finset A) : Set A) = ⊤`

we obtain `refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S`
with `S := C.covers.biUnion mk_S_D`.

`hZavyalov_per_E_of_per_D_construction` — wrapper supplying the existence
shape consumed upstream.

### 2.2 Standard-shape discharge (just landed)

`exists_refines_cover_per_E_of_standardShape` — **fully discharges the
goal** when the user supplies `f_D : RationalLocData A → A` witnessing
that each `D ∈ C.covers` is already a standard plus-piece:

- `h_shape : ∀ D ∈ C.covers,
              rationalOpen D.T D.s = rationalOpen (insert (f_D D) C.base.T) C.base.s`
- `h_span  : Ideal.span ((C.covers.image f_D : Finset A) : Set A) = ⊤`

Supporting helpers:
- `exists_single_f_refinement_of_standardShape` — pointwise version.
- `rationalOpen_eq_biInter_insert_union` — structural identity
  `R(F ∪ T, s) = (⋂ f ∈ F, R(insert f T, s)) ∩ R(T, s)`.
- `per_D_construction_of_standardShape` — per-D data assembly.

So **all that is missing** is a construction of `f_D` (or a multi-`F`
analogue `F_D : RationalLocData A → Finset A`) for an **arbitrary**
cover piece `D` whose `D.T` can be larger than one element.

### 2.3 C2 — quasi-compactness of rational opens (landed 2026-04-18, `SpaCompact.lean`)

Abstract theorem: from any closed description
`ιSpv_bool '' Spa A A⁺ = range ιSpv_bool ∩ S` (Bool Huber embedding),
the rational open `rationalOpen T s` is quasi-compact in `Spv A`.
Concrete suppliers:
- `isCompact_preimage_rationalOpen_of_tate_pseudouniformizer` (Tate case).
- `isCompact_preimage_rationalOpen_of_discreteTopology` (discrete case).

Route: clopen **cylinders** `{r | r(t,s) = true}` in the Bool product,
NOT closedness of basic opens in `Spv A`. (Naive "basic open clopen"
fails here; see §5.)

### 2.4 C3 — span-top from no-common-zero (already landed, `StandardCover.lean`)

`spanTop_iff_noCommonZero_spa` — the Prop 7.14 equivalence, **both
directions**, under `PairOfDefinition A` + `[IsAdicComplete]`:
`Ideal.span (T : Set A) = ⊤ ↔ ∀ v ∈ Spa A A⁺, ∃ t ∈ T, ¬ v.vle t 0`.

### 2.5 Cor 7.32 — dominating-unit extraction (`StandardCover.lean`)

```lean
theorem exists_dominating_unit_from_covering
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A,
      letI : ValuativeRel A := v.toValuativeRel
      MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (_C : RationalCovering A) (T : Finset A)
    (hT : ∀ v ∈ Spa A A⁺, ∃ t ∈ T, ¬ v.vle t 0) :
    ∃ σ : Aˣ, ∀ v ∈ Spa A A⁺, ∃ t ∈ T,
      v.vle (σ : A) t ∧ ¬ v.vle t (σ : A)
```

Reading: given `T` with no common zero on `Spa`, the unit `σ` is
"dominated by some element of `T`" at every Spa point — i.e., at every
`v ∈ Spa A A⁺`, some `t ∈ T` has `v(σ) < v(t)` strictly. This is the
Zavyalov/Wedhorn dominating-unit trick.

### 2.6 Other relevant APIs
- `rationalOpen_inter : R(T₁, s₁) ∩ R(T₂, s₂) = R(T₁ · T₂, s₁ · s₂)` (Wedhorn 7.30(5)).
- `rationalOpen_insert_s : R(insert s T, s) = R(T, s)` (7.30(3)).
- `rationalOpen_insert_of_vle : if ∀ v ∈ R(T, s), v.vle f s, then R(insert f T, s) = R(T, s)`.
- `refines_span_top_image_unit_mul` — if `T` spans the unit ideal, so does `σ⁻¹ · T`.
- `basicOpen_mul_subset : basicOpen (t·f) (t·s) ⊆ basicOpen f s`.
- `not_vle_zero_left_of_mul`, `not_vle_zero_right_of_mul` — `v(s₁·s₂) ≠ 0 ⇒ v(sᵢ) ≠ 0`.
- `ValuativeRel.mul_vle_mul`, `ValuativeRel.mul_vle_mul_left`, `ValuativeRel.mul_vle_mul_iff_left`.

## 3. The precise obstruction

Fix `D ∈ C.covers`. We want a finite family `F_D : Finset A` (ideally
a single `f_D : A`) such that:

(a) **Containment** — each plus-piece lands in `D`:
`∀ f ∈ F_D, rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s`.

(b) **Coverage** — plus-pieces-in-F_D together cover `D`:
`∀ v ∈ rationalOpen D.T D.s, ∃ f ∈ F_D, v ∈ rationalOpen (insert f C.base.T) C.base.s`.

(c) **Span** — across `D`, `Ideal.span ((⋃_D F_D : Finset A) : Set A) = ⊤`.

**Why single-`f` is hard.** The plus-piece `R(insert f T, s)` adds a
single inequality `w.vle f s`, i.e., `w(f) ≤ w(s)`. To force
`w ∈ R(D.T, D.s)`, we need *all* of `{w(t'ᵢ) ≤ w(D.s)}_{i}` plus
`w(D.s) ≠ 0`. Since `w(∏ tᵢ) = ∏ w(tᵢ)` is generally **not ≤ max w(tᵢ)**
in non-archimedean valuations, neither products nor sums of the
`t'ᵢ / D.s` ratios encode the conjunction correctly. The naive
candidates all fail.

**Multi-`F` is easier but the wrong shape.** Setting
`F_D ⊇ {σ·t'ᵢ·C.base.sⁿⁱ : t'ᵢ ∈ D.T}` for a suitable unit `σ` and
powers, one can arrange that `⋂ f ∈ F_D, R(insert f C.base.T, C.base.s)
= R(F_D ∪ C.base.T, C.base.s) ⊆ D`. But (a) in `refines_cover_per_E`
requires each INDIVIDUAL plus-piece ⊆ D, not just the joint
intersection. So multi-`F` does not plug in directly.

**Key missing content.** The Zavyalov §2.3 / Wedhorn §8.34 construction
exhibits specific elements `fᵢ ∈ A` such that each individual plus-piece
`R(insert fᵢ C.base.T, C.base.s)` lands in SOME cover piece `D`, AND
every point of `C.base` is in one of these plus-pieces. The text
defines them as ratios cleared by a dominating unit, but we have not
been able to transcribe the formula rigorously.

## 4. Concrete questions for the reviewer

1. **Formula for `fᵢ`.** What is the precise Zavyalov §2.3 candidate
   formula? We have two candidate sketches we cannot confirm:

   - **(Sketch A — per-piece unit-rescaling.)** For each
     `D ∈ C.covers` with `D.T = {t'₁, ..., t'_k}`, apply Cor 7.32 to
     `T := D.T ∪ {D.s}` to obtain a unit `σ_D`. Set
     `f_{D, i} := σ_D⁻¹ · t'ᵢ` (or `σ_D⁻¹ · D.s`). Does each plus-piece
     `R(insert f_{D,i} C.base.T, C.base.s)` land in `D`? Cor 7.32's
     conclusion gives `v(σ_D) < v(t)` for some `t ∈ T`, but this is
     per-valuation, not uniform — so a single `f_{D,i}` being a subset
     of `D` is not immediate.

   - **(Sketch B — product of ratios.)** `f_D := (∏ t'ᵢ) · σ · C.base.s^N`
     for some `N`. Fails in general because
     `v(∏ t'ᵢ) ≤ v(D.s)^k` combined with `v(f_D) ≤ v(C.base.s)` does
     not imply `v(t'ᵢ) ≤ v(D.s)` for each `i`.

   What is the correct formula, and what invariants does it satisfy at
   every Spa point?

2. **Single-`f` necessary, or does multi-`F` suffice?** The downstream
   shape is `refines_cover_per_E` (single-`f` per point). Is this
   genuinely forced by Wedhorn's proof of 8.28(b), or does a multi-`F`
   variant plus an intersection-refinement step suffice? In particular,
   does Hübner's 3.8 admit a "each point `v` is in the joint
   intersection of a finite family `F_v ⊆ S` of plus-pieces" shape, or
   is the per-point single-`f` form essential for the Čech assembly?

3. **Role of Cor 7.32 in denominator clearing.** Cor 7.32's output is a
   *per-point* dominating unit: at each `v`, some `t ∈ T` has
   `v(σ) < v(t)`. How does this pointwise statement translate into a
   UNIFORM bound (or a finite PARTITIONING of `Spa`) that lets us
   choose a single `f` with GLOBAL containment
   `R(insert f C.base.T, C.base.s) ⊆ R(D.T, D.s)`? Is the intended
   use to PARTITION `Spa` into finitely many pieces by which `t ∈ T`
   dominates, and construct one `f` per piece?

4. **Relevant Nullstellensatz outputs.** Beyond `spanTop_iff_noCommonZero_spa`
   (the equivalence between `Ideal.span = ⊤` and no common zero on
   Spa), what OTHER Prop 7.14 fragments does Zavyalov use for C1? We
   have access to:
   - "no common zero on Spa ⇒ dominating unit exists" (Cor 7.32).
   - "span = ⊤ ⇔ no common zero on Spa" (Prop 7.14).
   - "unit-rescaled family preserves unit-ideal span".
   - Spa-point producer at arbitrary primes (open + non-open via
     Lemma 7.45).

   Is there a further 7.14-adjacent statement we are missing
   (e.g., "finite common-zero locus has finite index", or the valuative
   criterion for specific ratios)?

5. **Lean-friendly lemma boundaries.** If the Zavyalov construction
   decomposes into several sub-lemmas, what are the natural
   intermediate statements that are both (i) provable from existing
   APIs above and (ii) combine to give C1? Ideally each sub-lemma
   should be single-page or less and not require new major
   infrastructure. Candidate shapes we have considered but cannot
   verify:

   - **(L1)** For any `D ⊆ C.base` and `v ∈ D`, there is an `f ∈ A`
     with `v(f) ≤ v(C.base.s)` and `∀ w ∈ C.base \ D, w(f) > w(C.base.s)`.
     (Spa-topological separator.) This directly gives single-`f`.
   - **(L2)** For any finite set of Spa points `{w_j} ⊆ C.base \ D`,
     there is an `f ∈ A` separating `v` from `{w_j}` as above.
     (Finite separator; combine with quasi-compactness of `C.base \ D`
     — but `C.base \ D` is closed and need not be open.)
   - **(L3)** For each `D ∈ C.covers`, the set
     `{f ∈ A | R(insert f C.base.T, C.base.s) ⊆ D}`
     generates an ideal, and this ideal is the unit ideal times the
     "boundary" of `D`.

   Which of these (or what alternative) is the right intermediate?

6. **Special cases first?** Can the general construction be staged as:
   - Case 1: `D.T = ∅` (only a denominator constraint). Then `D = R(∅, D.s)`; what is `f`?
   - Case 2: `|D.T| = 1` with `D.T = {t'}`. Then we need to encode just `w(t') ≤ w(D.s)` via `w(f) ≤ w(C.base.s)`. What is `f` as a function of `t', D.s, C.base.s`?
   - Case 3: `|D.T| ≥ 2`. Induct over `|D.T|` and split using `rationalOpen_inter`?

   Each case could be a landable theorem if the formula is explicit.

## 5. Why the "naive" compactness route was wrong (for context)

An earlier audit incorrectly claimed C2 follows from a non-existent
`basicOpen_isClopen` in `Spv A`. The SpaCompact preamble explicitly
warns that `{v | v.vle a 1} = basicOpen a 1` is **open, not closed**
in `Spv A`; the "closed-in-compact" route fails because rational opens
are quasi-compact opens of a spectral space, NOT clopen subsets. The
correct route (landed) uses clopen **cylinders** in the discrete Bool
product `(A × A → Bool)` via the Huber embedding `ιSpv_bool`, then
transfers compactness back via the embedding. Any proposed C1 argument
should NOT rely on basic/rational opens being closed in `Spv A` either.

## 6. Hypotheses in scope

The downstream consumer `tateAcyclicity_Part2_via_hZavyalov_per_E_direct`
runs under:

```
[CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A]
[IsHuberRing A] [IsTateRing A] [IsNoetherianRing A] [T2Space A]
[NonarchimedeanRing A] [DecidableEq A]
(P : PairOfDefinition A) [IsNoetherianRing P.A₀]
(C : RationalCovering A) (hne : C.covers.Nonempty)
```

Plus the pseudo-uniformizer data already consumed by Cor 7.32 and the
Tate compactness theorem (`π : P.A₀`, `hI : P.I = Ideal.span {π}`,
`hπ_tn`, `hπ_unit`, `hArch`). These are all standard Tate hypotheses.

## 7. What we emphatically do NOT want from the reviewer

- Guessed Lean proofs; we have not exhausted the algebra and do not
  want to nest Lean-specific technical issues on top.
- A full reformalisation of Prop 7.14; we already have
  `spanTop_iff_noCommonZero_spa` proved in both directions.
- A rederivation of C2 or C3; both are already landed and axiom-clean.

## 8. What we DO want

A clean statement of the Zavyalov §2.3 (or Hübner 3.8, or Wedhorn 8.34
inductive step) candidate formula, sufficient to translate into one or
two Lean lemmas, with:

- The precise algebraic expression for `f_{D, i}` (or `F_D`).
- The pointwise inequality argument that puts each plus-piece inside
  `D`.
- The coverage argument (every `v ∈ D` lies in some plus-piece).
- The span-top argument (combined family spans `⊤`).
- An explicit dependency on which Prop 7.14 / Cor 7.32 fragment is
  used where.

If the answer is "single-`f` is not needed, use `refines_cover_per_E`
via a multi-`F` refinement that we collapse by an inclusion-chain
argument," we would like to see that exact collapse stated as a
lemma: given multi-`F` coverage+containment, how do we produce the
single-`f` data required by `refines_cover_per_E`?
