/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.GroupScheme.Subgroup
import ModularCurves.LevelStructure.Basic

/-!
# Cyclic finite locally free subgroup schemes — the Γ₀(N) datum of record (T-SG2)

KM 1.4.1 (verbatim, quote in hand): *"a closed subgroup-scheme `G ⊆ C` which is finite
locally-free of rank `N` over `S` is **cyclic** if, locally f.p.p.f. (SGA III, Exp. IV,
6.3) on `S`, `G` admits a generator"*. This file names that adjective for the subgroup
scheme layer built in `T-SG1` (`FiniteLocallyFreeSubgroup`): `IsCyclic`, the Γ₀(N)
cyclicity **of record**, and packages the Γ₀(N)-structure datum `GammaZeroStructure` as a
cyclic finite locally free subgroup scheme.

## Definition of record — how the pieces fit

The literal f.p.p.f.-local cyclicity predicate already exists at the *divisor* layer as
`EllipticCurve.IsGammaZeroFppf` (ticket `T-D10`, `LevelStructure/Basic.lean`): a rank-`N`
subgroup divisor that f.p.p.f.-locally admits a generating section of exact order `N`
(`Σ_{a} [aP₀] = G`). `T-SG1` supplies the bridge `FiniteLocallyFreeSubgroup.toRelEffCartierDiv`
from a subgroup **scheme** to its underlying subgroup **divisor** (`IsSubgroup` proven,
degree = rank). So the cyclicity of record for a subgroup scheme is simply *its underlying
divisor is `IsGammaZeroFppf`*:

  `G.IsCyclic N := E.IsGammaZeroFppf N G.toRelEffCartierDiv`.

This reuses `T-D10` wholesale — **no new f.p.p.f. vocabulary is introduced** — and inherits
the review's GATE: representability of `Γ₀(N)` is stated against `IsCyclic` (the f.p.p.f.
form), never against the geometric-fibre surrogate `IsGammaZero`. The surrogate relates to
the record through `isGammaZero_iff_fppf` (KM 3.7.1, ⧗-gated, sorried in `T-D10`).

`IsGammaZeroFppf` bundles `IsSubgroup ∧ (degree = N) ∧ (∃ f.p.p.f. generator)`. For a
`FiniteLocallyFreeSubgroup` the `IsSubgroup` conjunct is automatic
(`toRelEffCartierDiv_isSubgroup`) and `degree = N` is exactly `HasRank N` transported along
`toRelEffCartierDiv_degree`; so `G.IsCyclic N` is faithfully KM's *"cyclic subgroup scheme
of order `N`"* (KM 3.4). This routes through `T-SG1`'s proven `toRelEffCartierDiv` bridge
and `T-D20`'s divisor base change only — it does **not** touch the parked base-change
subgroup field `T-SG1b`.

## Main definitions

* `FiniteLocallyFreeSubgroup.IsCyclic`: KM 1.4.1 cyclicity of record.
* `GammaZeroStructure`: a Γ₀(N)-structure — a cyclic finite locally free subgroup scheme
  of rank `N` (KM 3.4), the datum representability theorems must target.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}}

namespace FiniteLocallyFreeSubgroup

variable {E : EllipticCurve S}

-- Why this is the right definition:
-- * It is stated through the *divisor* `toRelEffCartierDiv`, whose base change (inside
--   `IsGammaZeroFppf`) is the proven `RelEffCartierDiv.baseChange` (T-D20) rather than the
--   parked subgroup base change (T-SG1b) — so it is sorry-free.
-- * The `IsSubgroup` conjunct of `IsGammaZeroFppf` is automatic here
--   (`toRelEffCartierDiv_isSubgroup`), so `IsCyclic` admits no inhabitant that a bare divisor
--   would admit.
-- * Rank is not a separate hypothesis: the `degree = N` conjunct forces `HasRank N` through
--   `toRelEffCartierDiv_degree` (see `IsCyclic.hasRank`), matching KM 3.4's "of order `N`".
-- * The case `p ∣ N` in characteristic `p` is included, unlike the geometric-fibre surrogate:
--   for supersingular `E`, `Ker F ⊆ E` is cyclic with Drinfeld generator `0`, and
--   `IsGammaZeroFppf` is correct there.
/-- **KM 1.4.1 cyclicity, the Γ₀(N) definition of record** for the subgroup-scheme layer:
a finite locally free subgroup scheme `G ⊆ E` is *cyclic of order `N`* when its underlying
subgroup divisor `G.toRelEffCartierDiv` is `IsGammaZeroFppf` — i.e. f.p.p.f.-locally on `S`
it admits a generating section of exact order `N`. Equivalently (KM 3.4): `G` is a rank-`N`
subgroup scheme that f.p.p.f.-locally admits a generator. -/
def IsCyclic (G : FiniteLocallyFreeSubgroup E) (N : ℕ) [NeZero N] : Prop :=
  E.IsGammaZeroFppf N G.toRelEffCartierDiv

/-- `IsCyclic` unfolds to `IsGammaZeroFppf` of the underlying divisor (definitional). -/
theorem isCyclic_iff_isGammaZeroFppf (G : FiniteLocallyFreeSubgroup E) (N : ℕ) [NeZero N] :
    G.IsCyclic N ↔ E.IsGammaZeroFppf N G.toRelEffCartierDiv :=
  Iff.rfl

/-- A cyclic subgroup scheme has (globally constant) rank `N` — KM 3.4's *"of order `N`"*,
extracted from the `degree = N` conjunct of `IsGammaZeroFppf` via `toRelEffCartierDiv_degree`. -/
theorem IsCyclic.hasRank {G : FiniteLocallyFreeSubgroup E} {N : ℕ} [NeZero N]
    (h : G.IsCyclic N) : G.HasRank N :=
  fun s => (G.toRelEffCartierDiv_degree s).symm.trans (h.2.1 s)

/-- The underlying divisor of a cyclic subgroup scheme is a subgroup divisor (the
`IsSubgroup` conjunct; also automatic from `toRelEffCartierDiv_isSubgroup`). -/
theorem IsCyclic.isSubgroup {G : FiniteLocallyFreeSubgroup E} {N : ℕ} [NeZero N]
    (h : G.IsCyclic N) : G.toRelEffCartierDiv.IsSubgroup E :=
  h.1

/-- The f.p.p.f. generator witnessing cyclicity: a faithfully-flat, locally finitely
presented, surjective cover `h : T ⟶ S` and a section `P₀` of `E ×_S T` of exact order `N`
whose order divisor `Σ_{a} [aP₀]` is `G` pulled back to `T` (KM 1.4.1's *"admits a
generator"*). -/
theorem IsCyclic.exists_fppf_generator {G : FiniteLocallyFreeSubgroup E} {N : ℕ} [NeZero N]
    (h : G.IsCyclic N) :
    ∃ (T : Scheme.{u}) (hT : T ⟶ S),
      Function.Surjective hT.base ∧ Flat hT ∧ LocallyOfFinitePresentation hT ∧
      ∃ P₀ : (E.baseChange hT).Section,
        P₀.HasExactOrder (E.baseChange hT) N ∧
        (P₀.orderDivisor (E.baseChange hT) N).ideal =
          (G.toRelEffCartierDiv.baseChange hT).ideal :=
  h.2.2

/-- **Constructor for `IsCyclic`**: a finite locally free subgroup scheme of rank `N` that
f.p.p.f.-locally admits a generating section of exact order `N` is cyclic. The `IsSubgroup`
and `degree = N` conjuncts of `IsGammaZeroFppf` are discharged from `T-SG1` data
(`toRelEffCartierDiv_isSubgroup`, `toRelEffCartierDiv_degree` + `HasRank`). -/
theorem isCyclic_of_generator {G : FiniteLocallyFreeSubgroup E} {N : ℕ} [NeZero N]
    (hrank : G.HasRank N) {T : Scheme.{u}} (hT : T ⟶ S)
    (hsurj : Function.Surjective hT.base) (hflat : Flat hT)
    (hlfp : LocallyOfFinitePresentation hT) (P₀ : (E.baseChange hT).Section)
    (hord : P₀.HasExactOrder (E.baseChange hT) N)
    (hgen : (P₀.orderDivisor (E.baseChange hT) N).ideal =
      (G.toRelEffCartierDiv.baseChange hT).ideal) :
    G.IsCyclic N :=
  ⟨G.toRelEffCartierDiv_isSubgroup,
    fun s => (G.toRelEffCartierDiv_degree s).trans (hrank s),
    ⟨T, hT, hsurj, hflat, hlfp, P₀, hord, hgen⟩⟩

end FiniteLocallyFreeSubgroup

-- Notes on the shape of this structure:
-- * `subgroup` is the datum (a `FiniteLocallyFreeSubgroup`, i.e. a `Type`), while `isCyclic`
--   and `hasRank` are `Prop` fields. The moduli problem quantifies over the whole structure,
--   so two structures with distinct total spaces are distinct terms; they are identified only
--   up to isomorphism, exactly as for T-SG1.
-- * `hasRank` is kept as a field even though `isCyclic.hasRank` derives it. KM 3.4 lists
--   "finite locally free of rank `N`" and "cyclic" as separate clauses, and downstream
--   rank-`N` hypotheses read `hasRank` directly rather than unfolding `IsGammaZeroFppf`. The
--   redundancy is a convenience, not a soundness gap: `isCyclic.hasRank = hasRank` for any
--   inhabitant.
-- * No representability is asserted here. This is only the datum that a `Γ₀(N)` moduli functor
--   quantifies over, and that functor must use this f.p.p.f. record rather than the
--   geometric-fibre surrogate `IsGammaZero`.
/-- **A Γ₀(N)-structure (KM 3.4), the datum of record**: a finite locally free subgroup
scheme `G ⊆ E` of rank `N` that is cyclic (KM 1.4.1, f.p.p.f. sense). This is what a
`Γ₀(N)` moduli problem quantifies over — the review's GATE requires representability to
target this f.p.p.f. record, not the geometric-fibre surrogate. -/
structure GammaZeroStructure (E : EllipticCurve S) (N : ℕ) [NeZero N] where
  /-- The cyclic subgroup scheme `G ⊆ E`. -/
  subgroup : FiniteLocallyFreeSubgroup E
  /-- `G` is cyclic of order `N` (KM 1.4.1, f.p.p.f. form of record). -/
  isCyclic : subgroup.IsCyclic N
  /-- `G` has rank `N` (KM 3.4 *"of order `N`"*; equals `isCyclic.hasRank`). -/
  hasRank : subgroup.HasRank N

namespace GammaZeroStructure

variable {E : EllipticCurve S}

/-- Build a Γ₀(N)-structure from just a cyclic subgroup scheme (rank `N` is derived). -/
def ofIsCyclic {N : ℕ} [NeZero N] (G : FiniteLocallyFreeSubgroup E) (h : G.IsCyclic N) :
    GammaZeroStructure E N where
  subgroup := G
  isCyclic := h
  hasRank := h.hasRank

@[simp]
theorem ofIsCyclic_subgroup {N : ℕ} [NeZero N] (G : FiniteLocallyFreeSubgroup E)
    (h : G.IsCyclic N) : (ofIsCyclic G h).subgroup = G :=
  rfl

/-- The subgroup scheme of a Γ₀(N)-structure has rank `N` — the order of the cyclic subgroup,
not the rank `N²` of the full `N`-torsion `E[N]`. -/
theorem rank_eq {N : ℕ} [NeZero N] (Γ : GammaZeroStructure E N) (s : S) :
    Γ.subgroup.rank s = N :=
  Γ.hasRank s

end GammaZeroStructure

end EllipticCurve

end ModularCurves
