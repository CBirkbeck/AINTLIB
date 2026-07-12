# /develop --decompose — [STREAM-FP] / [A711-FP]: finite presentation from module-finite + module-projective

*fable-FP, 2026-07-08. Charter: [STREAM-FP] (tickets.md §v10.37, claimed §v10.41). Target
file: NEW `ModularCurves/ForMathlib/FinitePresentationOfFinite.lean`. Discipline: v10.8
(this artifact), v10.24 (decompose-don't-grind), v10.35b (everything internal — this is an
internal deliverable; no upstream contact).*

---

## ★ HEADLINE FINDING — the substrate-absence verification is STALE

The charter says *"fable-P4 verified the substrate is genuinely absent from mathlib (no
constructor at all for FP-from-module-finite)"*. **On the current pin this is no longer
true.** The pinned mathlib contains

> `Mathlib/RingTheory/Finiteness/ModuleFinitePresentation.lean`
> (Christian Merten, copyright 2025; olean present in the cache, verified),

whose two main results are **exactly the delicate step**:

```
/-- EGA IV₁, 1.4.7.1 -/
lemma Module.Finite.exists_free_surjective [Module.Finite R S] :
    ∃ (S' : Type u) (_ : CommRing S') (_ : Algebra R S') (_ : Module.Finite R S')
      (_ : Module.Free R S') (_ : Algebra.FinitePresentation R S')
      (f : S' →ₐ[R] S), Function.Surjective f

/-- If `S` is finitely presented as a module over `R`, it is finitely
presented as an algebra over `R`. -/
instance Algebra.FinitePresentation.of_finitePresentation
    [Module.FinitePresentation R S] : Algebra.FinitePresentation R S
```

(verbatim from the pinned file, lines 35–39 and 68–71; the converse
`Module.FinitePresentation.of_finite_of_finitePresentation` is there too, tagged
`@[stacks 0564 "The case M = S"]`). Together with the long-standing
`Module.finitePresentation_of_projective` (`Mathlib/Algebra/Module/FinitePresentation.lean:154`,
deliberately **not** an instance — *"Ideally this should be an instance but it makes mathlib
much slower"*), the [A711-FP] statement is a **two-step assembly**, not a 300–500-line
development. The earlier verification was evidently made before the daily bump picked this
file up (or searched only `RingTheory/FinitePresentation.lean`, where the sole constructor
is indeed the noetherian `of_finiteType`).

**Consequence for the charter**: [A711-FP] discharges TODAY; the noetherian scaffold on the
étale-torsor layer comes off the same day (consumer flip below); the strong-worker budget
shifts to the stretch follow-ons ([KM-FMT-FLAT], then [NISOG-GRASS]).
**Board correction filed in §v10.41b.** No B2 — the boarded *statement* is exactly right;
only its "absent from mathlib" scoping note is stale.

---

## Top-level result (the [A711-FP] contract)

```lean
theorem Algebra.FinitePresentation.of_finite_of_projective
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Module.Projective R A] :
    Algebra.FinitePresentation R A
```

**Consumer contract check** (`ForMathlib/InvariantTorsor.lean:1021`): the noetherian
variant consumes precisely `Algebra.FinitePresentation (FixedPoints.subalgebra R A G) A`
with `Module.Finite` and `Module.Projective` instances already provided by proven
`of_isFreeAlgebraAction` theorems. Base ring = a `Subalgebra` coercion — covered by the
`Type*` polymorphism above. Statement matches the board's [A711-FP] wording verbatim
("a module-finite, module-projective algebra over an arbitrary commutative ring is of
algebra-level finite presentation").

### Prose proof A — the route the Lean proof actually takes (mathlib 2026)

1. `Module.Finite R A` + `Module.Projective R A` ⟹ `Module.FinitePresentation R A`.
   This is Stacks 00NX (2)⟹(1) (finite projective ⟹ finitely presented [and flat]);
   in mathlib it is literally `Module.finitePresentation_of_projective R A`.
2. `Module.FinitePresentation R A` ⟹ `Algebra.FinitePresentation R A`.
   This is EGA IV₁ 1.4.7 (b)⟹(a′) / the M = S case of Stacks 0564 read right-to-left;
   in mathlib it is the instance `Algebra.FinitePresentation.of_finitePresentation`.
   Assembly: `haveI := Module.finitePresentation_of_projective R A; inferInstance`.

### Prose proof B — the classical content (recorded so the delicacy is on file)

For the record, the proof *inside* the mathlib instance (= EGA IV₁ 1.4.7.1, = the S′
construction in Stacks 0564's proof):

1. Pick module generators y₁,…,yₙ of A over R. Each yᵢ is **integral** over R because A
   is module-finite (Cayley–Hamilton; Stacks 00GC "finite ⟹ integral"), so there are
   *monic* Pᵢ ∈ R[x] with Pᵢ(yᵢ) = 0.
2. Build the intermediate A′ = R[x₁,…,xₙ]/(P₁(x₁),…,Pₙ(xₙ)). Monicity makes A′ a **free**
   R-module on the monomials x₁^{e₁}⋯xₙ^{eₙ}, 0 ≤ eᵢ < deg Pᵢ (successive
   `AdjoinRoot`s of monic polynomials in mathlib), and A′ is visibly a finitely presented
   R-algebra. Map A′ ↠ A by xᵢ ↦ yᵢ; surjective since the yᵢ generate as a module.
3. The kernel of A′ ↠ A is finitely generated **as an ideal**: A′ is a finite R-module
   and A is a finitely presented R-module, so ker is a finitely generated R-submodule
   (Stacks 0519(5) shape; mathlib `Module.FinitePresentation.fg_ker`), hence a fortiori a
   finitely generated ideal (`Submodule.FG.of_restrictScalars` — restriction of scalars
   along R → A′). This is THE step where "finitely presented as a module" replaces
   noetherianity; over a noetherian base every ideal of A′ is f.g. and the delicacy
   vanishes — exactly KM's warning.
4. A ≅ A′/ker with A′ algebra-FP and ker ideal-f.g. ⟹ A is algebra-FP
   (`Algebra.FinitePresentation.of_surjective`).

The multiplication-table route (surjection R[X₁..Xₙ] ↠ A; sub-ideal J from the table
xᵢxⱼ = Σ cᵢⱼₖ xₖ and 1 = Σ dₖ xₖ; R[X]/J module-finite; split off the kernel by
projectivity) proves the same thing and was the planned fallback; not needed.

---

## Ordered leaf decomposition

Two leaves, strictly ordered. No artificial padding: both inputs of [FP-A] are single
mathlib citations, and inventing intermediate leaves would re-prove mathlib (the cardinal
sin).

### [FP-A] `Algebra.FinitePresentation.of_finite_of_projective` — the [A711-FP] statement
- **File**: `ForMathlib/FinitePresentationOfFinite.lean` (NEW; no project imports — pure
  mathlib on both sides, upstream-shaped).
- **Proof**: prose proof A. Expected ≤ 5 lines.
- **Sources + verbatim quotes**: §Quotes items 1, 2, 3, 6 below.
- **Lean↔source match**: Stacks 00NX condition (2) "M is finite projective" is the
  conjunction `[Module.Finite R A] [Module.Projective R A]` (mathlib's
  `Module.Projective` = lifting property ⟺ direct-summand-of-free, 00NX (3), via
  `Module.Projective.of_split`/`Finite.exists_comp_eq_id_of_projective`); 00NX
  condition (1) "M is finitely presented and R-flat" restricted to its first conjunct is
  `Module.FinitePresentation R A`, and `Module.finitePresentation_of_projective` is
  precisely (2)⟹(1)₁. EGA IV₁ 1.4.7 (b) "B est un A-module de présentation finie" ⟹
  (a′) "B est une A-algèbre de présentation finie" is
  `Algebra.FinitePresentation.of_finitePresentation` — mathlib's own docstring/citation
  ("EGA IV₁, 1.4.7.1" on the auxiliary construction) pins the correspondence; the
  auxiliary S′ of `exists_free_surjective` is the S′ = R[x₁..xₙ]/(Pᵢ(xᵢ)) of Stacks
  0564's proof, built one `AdjoinRoot ((minpoly R a).map …)` at a time.

### [FP-B] the consumer flip — `Algebra.Etale.of_isFreeAlgebraAction` (general base)
- **File**: `ForMathlib/InvariantTorsor.lean:728` (the file's ONE remaining sorry).
  **Held-file protocol**: fable-P4's live focus is EngineDescent.lean ([a2]); git shows
  InvariantTorsor.lean clean (no in-flight edits). Surgical edit under a separate board
  claim line (§v10.41b): ONE import + ONE proof body + docstring status update; the
  statement is untouched per the frozen-signature rule. Pathspec commit of exactly that
  file.
- **Proof**: mirror the proven noetherian assembly (`…_of_isNoetherianRing`,
  InvariantTorsor.lean:1012–1025) verbatim, with the single line
  `(Algebra.FinitePresentation.of_finiteType).mp inferInstance` (noetherian) replaced by
  `Algebra.FinitePresentation.of_finite_of_projective _ _` ([FP-A]), and the
  `[IsNoetherianRing …]` hypothesis gone.
- **Sources + verbatim quotes**: §Quotes items 4, 5 below.
- **Lean↔source match**: Stacks 08WD (3)⟹(1): "flat, unramified, and of finite
  presentation ⟹ étale" is mathlib's `Algebra.Etale.of_formallyUnramified_of_flat`
  (project comment at InvariantTorsor.lean:995–996 already pins this, "Stacks 08WD
  (3)⟹(1)"). Flat ⟸ projective (`Module.Flat.of_projective`); unramified =
  `Algebra.FormallyUnramified.of_isFreeAlgebraAction` (proven, separability idempotent);
  finite presentation = [FP-A]. KM A7.1.1's étaleness clause is thereby proved over an
  arbitrary invariant ring, discharging KM's "rather delicate" caveat via
  Chase–Harrison–Rosenberg-style inputs already in the file (no SGA III Exp. V needed).

---

## Verbatim source quotes (fetched 2026-07-08, per v10.8 — never from memory)

1. **Stacks Tag 00NX = Lemma 10.78.2** (fetched from stacks.math.columbia.edu/tag/00NX):
   > "For a ring R and R-module M, the following are equivalent: (1) M is finitely
   > presented and R-flat, (2) M is finite projective, (3) M is a direct summand of a
   > finite free R-module, (4) M is finitely presented and M_𝔭 is free for all
   > 𝔭 ∈ Spec(R), (5) M is finitely presented and M_𝔪 is free for all maximal ideals 𝔪,
   > (6) M is finite and locally free, (7) M is finite locally free, (8) M is finite,
   > M_𝔭 is free for every prime 𝔭, and the rank function ρ_M: Spec(R) → ℤ is locally
   > constant in the Zariski topology."
   Direction used by [FP-A]: (2)⟹(1), first conjunct.

2. **Stacks Tag 0564 = Lemma 10.36.23** (fetched from stacks.math.columbia.edu/tag/0564;
   the tag mathlib itself stamps on the converse):
   > "Let R → S be a finite and finitely presented ring map. Let M be an S-module. Then
   > M is finitely presented as an R-module if and only if M is finitely presented as an
   > S-module."
   Proof construction (as fetched): "choosing generators y₁, …, yₙ of S over R, finding
   monic polynomials Pᵢ(x) ∈ R[x] with Pᵢ(yᵢ) = 0, and considering the intermediate ring
   S' = R[x₁, …, xₙ]/(P₁(x₁), …, Pₙ(xₙ))" … "S' is free as an R-module, with basis given
   by monomials x₁^{e₁} ⋯ xₙ^{eₙ} where 0 ≤ eᵢ < deg(Pᵢ)" — the exact shape of mathlib's
   `Module.Finite.exists_free_surjective`.

3. **EGA IV₁, 1.4.7 / 1.4.7.1** — cited **via mathlib's own attribution** (docstring
   "EGA IV₁, 1.4.7.1" in `RingTheory/Finiteness/ModuleFinitePresentation.lean`; file
   header "References: [Grothendieck, EGA IV₁ 1.4.7][ega-iv-1]"). EGA is not in
   `refs/` and was not re-derived from memory; the Lean text itself is the transcription
   of record here.

4. **Stacks Tag 08WD = Lemma 10.151.8** (fetched from stacks.math.columbia.edu/tag/08WD):
   > "Let R → S be a ring map. The following are equivalent: (1) R → S is étale, (2)
   > R → S is flat and G-unramified, and (3) R → S is flat, unramified, and of finite
   > presentation."
   Direction used by [FP-B]: (3)⟹(1).

5. **Katz–Mazur, Appendix A7.1.1** (book pp. 215–218, pdf 226–229; quote banked on the
   board at T-Q2/§v10.4-era and re-verified there — the FULL pdf's text layer does not
   expose this page to grep, so the board's banked transcription is the record): KM defers
   the torsor/étale statement to **SGA III Exp. V Thm 4.1** and warns:
   > "In the absence of noetherian hypotheses, this is rather delicate."
   [FP-A]+[FP-B] discharge exactly this caveat for the étaleness clause.

6. **Charter territory pointers, resolved** (per v10.8 "fetch, transcribe" — recorded for
   honesty about what the given tags actually are):
   - **Tag 00QQ = Lemma 10.126.2** (fetched): "Let R → S be a ring map. Let R → R' be a
     faithfully flat ring map. Set S' = R' ⊗_R S. Then R → S is of finite presentation if
     and only if R' → S' is of finite presentation." — the same *section* (algebras and
     modules of finite presentation), not the crux lemma itself.
   - **Tag 05GH = Lemma 10.97.5** (fetched): completion of a ring with f.g. ideal and
     noetherian quotient is noetherian — a mis-pointer (noetherian-completion territory);
     superseded by 0564/00NX/EGA 1.4.7 above as the leaves' actual sources.

---

## Adversarial blocks (standing rule 1, ≥3 attacks per leaf)

### [FP-A]
1. **"The instance can't exist — it would make FP-from-finite trivial everywhere"**:
   checked the pinned file byte-for-byte; `of_finitePresentation` takes
   `Module.FinitePresentation` (presented, not just finite) — no contradiction with the
   noetherian iff `of_finiteType` remaining the only constructor in
   `RingTheory/FinitePresentation.lean`. The delicate content lives in
   `exists_free_surjective`'s integrality induction. Attack fails; statement true.
2. **Instance-search trap**: `Module.finitePresentation_of_projective` is deliberately
   NOT an instance ("makes mathlib much slower" — comment at its site), so a bare
   `inferInstance`/`infer_instance` on the goal WILL fail without first `haveI`-ing the
   module-level FP. The 2-liner must thread it explicitly. Mitigated in the skeleton.
3. **Universe attack**: `exists_free_surjective` fixes `S' : Type u` = R's universe; our
   consumer instantiates R := ↥(FixedPoints.subalgebra R A G) (same universe as A). The
   instance is `(R : Type u) (S : Type*)`-polymorphic; no constraint links S to u in the
   *statement*, so the consumer's universes are unconstrained. Verified against the
   consumer by building [FP-B], not just [FP-A].
4. **Wrong-level attack** (algebra vs ring-hom FP): the consumer needs
   `Algebra.FinitePresentation`, not `RingHom.FinitePresentation`; statement is pinned to
   the former (they are defeq-transferable via `RingHom.finitePresentation_algebraMap`,
   not needed here).

### [FP-B]
1. **Sweep risk (the real one)**: root `ModularCurves.lean` carries p0's uncommitted
   import line; ANY pathspec commit touching it would sweep. Mitigation: do NOT register
   the new file in the root module at all — it enters the import graph transitively via
   InvariantTorsor.lean at flip time. InvariantTorsor.lean itself verified clean in git
   before the surgical edit; claim line on the board first.
2. **Statement-freeze attack**: the flip must not alter the theorem statement (rule:
   never change a statement to make something pass). The edit replaces only `by sorry`
   and the stale docstring paragraph; signature byte-identical.
3. **Assembly-mismatch attack**: could the general assembly need `FormallySmooth`
   ([A711-SM])? No — board §"08WD — [A711-SM] DISSOLVED outright"; the noetherian twin
   (proven, in-file) already assembles étale from unramified + flat + FP alone; the flip
   changes exactly one `haveI`.
4. **Instance-diamond attack at the subalgebra base**: the `Module.Finite`/`Projective`/
   `Flat` instances over `FixedPoints.subalgebra R A G` arrive via `haveI` from
   `of_isFreeAlgebraAction` theorems — identical shape to the proven noetherian twin, so
   no new diamond surface. If elaboration slows: v10.24, split, never grind.

---

## Skeleton

`ForMathlib/FinitePresentationOfFinite.lean` ships with [FP-A] `:= by sorry` and must
`lake build` green as target `ModularCurves.ForMathlib.FinitePresentationOfFinite`
(root registration deliberately deferred — see [FP-B] attack 1). [FP-B]'s skeleton is the
already-boarded sorry at InvariantTorsor.lean:730 (no new skeleton needed).

## Leaf tickets

Boarded as **[FP-A]**, **[FP-B]** in tickets.md §v10.41b (claims: fable-FP; [FP-B]'s
surgical-edit claim line included there).

## Stretch queue (charter order, after FP)
[KM-FMT-FLAT] → [NISOG-GRASS]; separate /develop --decompose artifacts when picked up.
