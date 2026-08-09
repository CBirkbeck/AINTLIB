/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.KMUniqueness

/-!
# Bilinearity and `μ_N` for the Katz–Mazur pairing (ticket AP-D7)

`WeilPairing/KMUniqueness.lean` builds `h(P)` — `torsionSplittingEval` — as a genuine function
of the data, with a spec (`resUnit_torsionSplittingEval`) valid for *every* normalised splitting
and a pin (`eq_torsionSplittingEval`). This file is Katz–Mazur p. 89's last two sentences: the
pairing is bilinear, and it lands in `μ_N`.

## What the two conclusions actually need

Both reduce, by the pin, to a statement about **splitting units over one fixed cover**, and both
then bottom out in the *same* module-level fact — see "The one open brick" below.

* Multiplicativity in `Q` is `eq_of_normalized_splitting` applied to `h_i · h'_i`: if the
  transition cocycles multiply, `f''_{i,j} = f_{i,j} · f'_{i,j}`, then `h_i · h'_i` is a
  normalised splitting of the pulled-back `f''`, and `sectionEval` is a monoid homomorphism.
* `h(P)^N = 1` is `eq_of_normalized_splitting` applied to `h_i^N`: if `f_{i,j}^N = g_i · g_j⁻¹`
  on the **curve** — the `g_i` need not be normalised, `exists_normalized_splitting` normalises
  them — then `h_i^N` and `g_i ∘ [N]` are two normalised splittings of `f_{i,j}^N ∘ [N]` over the
  cover `[N]⁻¹(W i)` of the curve, hence equal; and `g_i ∘ [N] ∘ P = g_i ∘ 0 = 1` since `[N]P = 0`.

## Two corrections to the boarded route

1. `h(P)^N = 1` does **not** follow from `(★′)` plus `eq_one_of_mem_kUnits` (AP-D2). AP-D2 pins a
   normalised unit only on the preimage of a *base* open, and `h_i` lives on `[N]⁻¹(W i)`, which
   is not of that form (if it were, `h_i` would be `1` and the pairing trivial). What replaces it
   is `eq_of_normalized_splitting` (`WeilPairing/KMUniqueness.lean`), i.e. AP-D2 *after* the
   ratios have been glued over a cover of the curve — and that is exactly why its covering
   hypothesis `iSup W = ⊤` is carried through every statement below.
2. KM's *"because `(Ker π)(S)` is killed by `N`"* is additivity in `P` specialised at `N • P = 0`,
   not an independent argument: `h(P)^N = h(N • P) = h(0) = 1`. That route needs translations
   (see `torsionSplittingEval_add`); the route taken here instead gets `h(P)^N = 1` from the
   `N`-th power cocycle directly, and so is independent of additivity in `P`.

## The one open brick

`exists_pow_transitionUnitOfCover_split` — the transition cocycle of `M^{⊗N}` is
`f_{i,j}^N`, and `M^{⊗N}` is trivial because `κ(Q)^N = κ(N • Q) = 1`. Everything in that sentence
except the first clause is proved (`kappa_nsmul`, `kappa_zero`,
`exists_transitionUnit_eq_mul_inv`); the first clause is the missing API
"`trivializationTransitionUnit` is monoidal", of which the tree has **no** instance — a grep for
`tensorObj` against `trivializationTransitionUnit`/`over`/`restrictOverTrivialization` finds
nothing. The identical brick, in its `M ⊗ M'` rather than `M^{⊗N}` form, is what upgrades
`torsionSplittingEval_mul_of_transitionUnitOfCover_mul` to bilinearity in `Q` for `Q + Q'`
through `kappa_add`.

## Main results

* `torsionSplittingEval_zero` — **`h(0) = 1`**, proved. The `P = 0` case of bilinearity, and the
  statement that pins the normalisation: it is exactly the assertion that the `h_i` are `1` along
  the zero section.
* `torsionSplittingEval_mul_of_transitionUnitOfCover_mul` — **bilinearity in `Q`, proved** in the
  cocycle form: over one cover, if the transition units multiply then `h(P)` multiplies. `Q''` is
  not required to be `Q + Q'`; the whole content is the cocycle identity, and `kappa_add` is what
  supplies it for `Q'' = Q + Q'` once the brick above is available.
* `torsionSplittingEval_pow_eq_one_of_split` — **`h(P)^N = 1`, proved** from any splitting of the
  `N`-th power cocycle on the curve (normalisation of that splitting is derived, not assumed).
* `torsionSplittingEval_pow_eq_one` — **the `μ_N` landing, KM p. 89**, unconditional.
  **Inherits `sorryAx`** through the one brick, and only through it.
* `torsionSplittingEval_add` — bilinearity in `P`. **`sorry`**; see its docstring.

## What is *not* used

Nothing here touches `exists_torsionPoint_of_mem_kerMulByN` (`WeilPairing/KMPairing.lean`, the
AP-D4 `⊇` direction), so no declaration below inherits *that* `sorryAx`. Only the proved `⊆`
direction enters, through AP-D5.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
  AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

/-- Rearranging a product of ratios in a commutative group. Stated over abstract elements so the
normalisation runs on atoms rather than on section terms. -/
private theorem mul_inv_mul_mul_inv {G : Type*} [CommGroup G] (a b c d : G) :
    a * b⁻¹ * (c * d⁻¹) = a * c * (b * d)⁻¹ := by
  simp only [mul_inv, mul_assoc, mul_left_comm]

/-- A ratio raised to a power. Kept as a lemma applied by `exact` rather than as a `rw`, because
the ambient `Γ` is indexed by `[N]⁻¹(W i ⊓ W j)`, which is only *definitionally* the intersection
`[N]⁻¹W i ⊓ [N]⁻¹W j`, and `rw` builds its motive at a transparency that does not see that. -/
private theorem mul_inv_pow {G : Type*} [CommGroup G] (a b : G) (n : ℕ) :
    (a * b⁻¹) ^ n = a ^ n * (b ^ n)⁻¹ := by
  rw [mul_pow, inv_pow]

/-- Evaluating along a section that *equals* the zero section kills a normalised unit. Stated with
the equality of sections as a hypothesis, and discharged by `subst`, because the open on which
`sectionEval z V` lands depends on `z`: rewriting `z` inside the goal is a dependent rewrite. -/
private theorem sectionEval_eq_one_of_eq {Y T : Scheme.{u}} {z z' : T ⟶ Y} (hzz : z = z')
    (V : Y.Opens) (u : Γ(Y, V)ˣ) (hu : u ∈ sectionUnits z' V) : sectionEval z V u = 1 := by
  subst hzz
  exact hu

section Curve

variable {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}
variable (hsm : SmoothOfRelativeDimension 1 E.π) [IsSeparated E.π] (t : T ⟶ S)
variable (N : ℕ) (Q : (E.baseChange t).Point (𝟙 T)) (hQ : Q ∈ torsionPoints E t N)
variable (M : (pullback E.π t).Modules)
variable (hM : letI := Scheme.Modules.monoidalCategory (pullback E.π t)
  (kappa E hsm t Q).val = toSkeleton M)
variable {ι : Type*} (W : ι → (pullback E.π t).Opens) (hW : iSup W = ⊤)
variable (e : ∀ i, M.over (W i) ≅
  _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (W i)))
variable (hnorm : ∀ i j, transitionUnitOfCover M W e i j ∈
  sectionUnits (baseChangeZero E.π E.zero E.zero_π t) (W i ⊓ W j))

/-! ## `h(0) = 1` -/

/-- **(KM p. 89, the normalisation at work)** `h(0) = 1`: the pairing is trivial on the zero
section. This is the `P = 0` case of bilinearity in `P`, and it is the *only* place the
normalisation of the `h_i` is visible in the value of `h`: `h(0) = h_i ∘ 0 = 1`.

Proved from the pin `eq_torsionSplittingEval` with `C = 1`. -/
theorem torsionSplittingEval_zero :
    torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm 0 (zero_mem _) = 1 := by
  obtain ⟨h, hn, hsplit⟩ :=
    exists_normalized_transitionUnit_eq_mul_inv_of_mem_torsionPoints E hsm t N Q hQ M hM W hW e
      hnorm
  have hzval : ((0 : (E.baseChange t).Point (𝟙 T)).1 : T ⟶ pullback E.π t) =
      baseChangeZero E.π E.zero E.zero_π t :=
    ((E.baseChange t).point_zero_val (𝟙 T)).trans (Category.id_comp _)
  refine (eq_torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm 0 (zero_mem _) h hn hsplit
    (C := 1) fun i => ?_).symm
  rw [map_one]
  exact (sectionEval_eq_one_of_eq hzval _ (h i) (hn i)).symm

/-! ## Bilinearity in `Q` -/

/-- **(KM p. 89, bilinearity in the second variable)** If three invertible sheaves are trivialised
over **one** cover `W` of the curve, with normalised transition cocycles satisfying
`f''_{i,j} = f_{i,j} · f'_{i,j}`, then their pairings against `P` multiply:

  `h''(P) = h(P) · h'(P)`.

The sections `Q, Q', Q''` are unconstrained beyond being `N`-torsion — in particular `Q''` is
*not* assumed to be `Q + Q'`. That is deliberate: the entire content is the cocycle identity, and
`Q'' = Q + Q'` enters only through `kappa_add` (`Picard/SelfAdjointN.lean`), which says that
`M ⊗ M'` represents `κ(Q + Q')` and hence — via the brick
`exists_pow_transitionUnitOfCover_split`'s `M ⊗ M'` analogue — that a trivialisation
`e''` with the required cocycle identity exists.

Proof: `h_i · h'_i` is a normalised splitting of `f''_{i,j} ∘ [N]`, and both `Scheme.resUnit` and
`sectionEval` are monoid homomorphisms, so `h(P) · h'(P)` satisfies the spec of `h''(P)`; the pin
`eq_torsionSplittingEval` finishes. -/
theorem torsionSplittingEval_mul_of_transitionUnitOfCover_mul
    (Q' Q'' : (E.baseChange t).Point (𝟙 T))
    (hQ' : Q' ∈ torsionPoints E t N) (hQ'' : Q'' ∈ torsionPoints E t N)
    (M' M'' : (pullback E.π t).Modules)
    (hM' : letI := Scheme.Modules.monoidalCategory (pullback E.π t)
      (kappa E hsm t Q').val = toSkeleton M')
    (hM'' : letI := Scheme.Modules.monoidalCategory (pullback E.π t)
      (kappa E hsm t Q'').val = toSkeleton M'')
    (e' : ∀ i, M'.over (W i) ≅
      _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (W i)))
    (e'' : ∀ i, M''.over (W i) ≅
      _root_.SheafOfModules.unit ((pullback E.π t).ringCatSheaf.over (W i)))
    (hnorm' : ∀ i j, transitionUnitOfCover M' W e' i j ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π t) (W i ⊓ W j))
    (hnorm'' : ∀ i j, transitionUnitOfCover M'' W e'' i j ∈
      sectionUnits (baseChangeZero E.π E.zero E.zero_π t) (W i ⊓ W j))
    (hmul : ∀ i j, transitionUnitOfCover M'' W e'' i j =
      transitionUnitOfCover M W e i j * transitionUnitOfCover M' W e' i j)
    (P : (E.baseChange t).Point (𝟙 T)) (hP : P ∈ torsionPoints E t N) :
    torsionSplittingEval E hsm t N Q'' hQ'' M'' hM'' W hW e'' hnorm'' P hP =
      torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P hP *
        torsionSplittingEval E hsm t N Q' hQ' M' hM' W hW e' hnorm' P hP := by
  obtain ⟨h, hn, hsplit⟩ :=
    exists_normalized_transitionUnit_eq_mul_inv_of_mem_torsionPoints E hsm t N Q hQ M hM W hW e
      hnorm
  obtain ⟨h', hn', hsplit'⟩ :=
    exists_normalized_transitionUnit_eq_mul_inv_of_mem_torsionPoints E hsm t N Q' hQ' M' hM' W hW
      e' hnorm'
  refine (eq_torsionSplittingEval E hsm t N Q'' hQ'' M'' hM'' W hW e'' hnorm'' P hP
    (fun i => h i * h' i) (fun i => Subgroup.mul_mem _ (hn i) (hn' i)) (fun i j => ?_)
    (fun i => ?_)).symm
  · rw [hmul i j, map_mul, hsplit i j, hsplit' i j, map_mul, map_mul]
    exact mul_inv_mul_mul_inv _ _ _ _
  · rw [map_mul,
      resUnit_torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P hP h hn hsplit i,
      resUnit_torsionSplittingEval E hsm t N Q' hQ' M' hM' W hW e' hnorm' P hP h' hn' hsplit' i]
    exact (map_mul (sectionEval (P.1 : T ⟶ pullback E.π t) (mulByN E t N ⁻¹ᵁ W i))
      (h i) (h' i)).symm

/-! ## Landing in `μ_N` -/

/-- **(KM p. 89, `h(P)^N = 1`)** If the `N`-th power of the transition cocycle splits on the
**curve**, `f_{i,j}^N = g_i · g_j⁻¹`, then the pairing is killed by `N`.

The `g_i` are *not* assumed normalised along the zero section: that is derivable, because
`f_{i,j}^N` is normalised (`pow_mem hnorm`) and the traces `0⁻¹(W i)` cover the base, so
`exists_normalized_splitting` (`WeilPairing/KMNormalisation.lean`) normalises any splitting. So
the hypothesis is exactly *"the `N`-th power cocycle is a coboundary on the curve"*, nothing more.

The two normalised splittings of the pulled-back `N`-th power cocycle `f_{i,j}^N ∘ [N]` over the
cover `[N]⁻¹(W i)` are then `h_i^N` and `g_i ∘ [N]` — the latter is normalised because
`[N] ∘ 0 = 0` (`zero_comp_mulByHom_baseChange`) — so `eq_of_normalized_splitting` identifies them;
and `h_i^N ∘ P = g_i ∘ [N] ∘ P = g_i ∘ 0 = 1` because `[N]P = 0`. The covering hypothesis `hW` is
doing real work three times: for the normalisation, for `eq_of_normalized_splitting` (which is
false without it) and for the final locality of units. -/
theorem torsionSplittingEval_pow_eq_one_of_split
    (P : (E.baseChange t).Point (𝟙 T)) (hP : P ∈ torsionPoints E t N)
    (g₀ : ∀ i, Γ(pullback E.π t, W i)ˣ)
    (hg₀ : ∀ i j, transitionUnitOfCover M W e i j ^ N =
      Scheme.resUnit (inf_le_left : W i ⊓ W j ≤ W i) (g₀ i) *
        (Scheme.resUnit (inf_le_right : W i ⊓ W j ≤ W j) (g₀ j))⁻¹) :
    torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P hP ^ N = 1 := by
  obtain ⟨g, hgn, hgsplit⟩ := exists_normalized_splitting
    (baseChangeZero_snd E.π E.zero E.zero_π t) W
    ((baseChangeZero E.π E.zero E.zero_π t).iSup_preimage_eq_top hW)
    (fun i j => transitionUnitOfCover M W e i j ^ N) g₀ hg₀
    (fun i j => pow_mem (hnorm i j) N)
  obtain ⟨h, hn, hsplit⟩ :=
    exists_normalized_transitionUnit_eq_mul_inv_of_mem_torsionPoints E hsm t N Q hQ M hM W hW e
      hnorm
  have hkey : ∀ i, h i ^ N =
      Units.map ((mulByN E t N).app (W i)).hom.toMonoidHom (g i) :=
    eq_of_normalized_splitting t E.toEllipticCurveGeom.universallyOConnected
      (baseChangeZero_snd E.π E.zero E.zero_π t) (fun i => mulByN E t N ⁻¹ᵁ W i)
      ((mulByN E t N).iSup_preimage_eq_top hW)
      (F := fun i j => Units.map ((mulByN E t N).app (W i ⊓ W j)).hom.toMonoidHom
        (transitionUnitOfCover M W e i j ^ N))
      (fun i => pow_mem (hn i) N)
      (fun i => mem_sectionUnits_pullback (zero_comp_mulByHom_baseChange E t (N : ℤ)) (W i)
        (hgn i))
      (fun i j => by
        rw [map_pow, hsplit i j, map_pow, map_pow]
        exact mul_inv_pow _ _ _)
      (fun i j => by
        rw [hgsplit i j, map_mul, map_inv, ← resUnit_map_app, ← resUnit_map_app]
        rfl)
  refine eq_of_forall_resUnit_eq
    (fun i => (P.1 : T ⟶ pullback E.π t) ⁻¹ᵁ (mulByN E t N ⁻¹ᵁ W i))
    (iSup_preimage_preimage_eq_top (mulByN E t N) (P.1 : T ⟶ pullback E.π t) hW) fun i => ?_
  rw [map_one, map_pow,
    resUnit_torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P hP h hn hsplit i]
  exact (map_pow (sectionEval (P.1 : T ⟶ pullback E.π t) (mulByN E t N ⁻¹ᵁ W i)) (h i) N).symm.trans
    (((congrArg (sectionEval (P.1 : T ⟶ pullback E.π t) (mulByN E t N ⁻¹ᵁ W i)) (hkey i)).trans
        (sectionEval_pullback (mulByN E t N) (P.1 : T ⟶ pullback E.π t) (W i) (g i))).trans
      (sectionEval_eq_one_of_eq (comp_mulByN_eq_baseChangeZero E t N P hP) (W i) (g i) (hgn i)))

include hsm hQ hM in
/-- **(THE ONE OPEN BRICK OF AP-D7 — `sorry`)** The `N`-th power of the transition cocycle of an
invertible sheaf representing `κ(Q)`, for `Q` an `N`-torsion section, is a coboundary on the
curve.

**Why it is true.** `κ(Q)^N = κ(N • Q) = κ(0) = 1` (`kappa_nsmul`, `kappa_zero`,
`Picard/SelfAdjointN.lean` — both proved and axiom-clean), so the `N`-th tensor power `M^{⊗N}` is
globally trivial. Its transition cocycle with respect to the induced trivialisations `e_i^{⊗N}` is
`f_{i,j}^N`, so `exists_transitionUnit_eq_mul_inv` (`WeilPairing/KMSplitting.lean`) splits it.
Neither `hW` nor `hnorm` is needed: the consumer
`torsionSplittingEval_pow_eq_one_of_split` normalises the splitting itself.

**What is missing.** Exactly one clause: *the transition cocycle of `M^{⊗N}` is `f_{i,j}^N`*, i.e.
that `trivializationTransitionUnit` is monoidal. The tree has no tensor API for it at all —
`Picard/InvertibleSheafCocycle.lean` proves `trivializationTransitionUnit` is reflexive, symmetric,
transitive (`_self`, `_symm`, `_trans`) and compatible with restriction and with pullback
(`_restrict`, `..._localPullbackTrivialization`), but nothing about `tensorObj`. Supplying it means
building `(M ⊗ M').over U ≅ M.over U ⊗ M'.over U`, `unit ⊗ unit ≅ unit` and the multiplicativity of
`overUnitScalarEnd` in the monoidal structure on `X.Modules`, which is a self-contained ticket.

**The same brick, in its `M ⊗ M'` rather than `M^{⊗N}` form, is what supplies the hypothesis
`hmul` of `torsionSplittingEval_mul_of_transitionUnitOfCover_mul` for `Q'' = Q + Q'` via
`kappa_add`.** So AP-D7's two conclusions have a single common obstruction, and it is a
module-level one: nothing about `h(P)` itself is open. -/
theorem exists_pow_transitionUnitOfCover_split :
    ∃ g : ∀ i, Γ(pullback E.π t, W i)ˣ,
      ∀ i j, transitionUnitOfCover M W e i j ^ N =
        Scheme.resUnit (inf_le_left : W i ⊓ W j ≤ W i) (g i) *
          (Scheme.resUnit (inf_le_right : W i ⊓ W j ≤ W j) (g j))⁻¹ := by
  sorry

/-- **(AP-D7, the `μ_N` landing — KM p. 89)** The Katz–Mazur pairing takes values in `μ_N`:
`h(P)^N = 1` in `Γ(T, 𝒪_T^×)`.

**Depends on `sorryAx`**, through `exists_pow_transitionUnitOfCover_split` and only through it;
`torsionSplittingEval_pow_eq_one_of_split`, which carries all the geometry, is proved and
axiom-clean. -/
theorem torsionSplittingEval_pow_eq_one
    (P : (E.baseChange t).Point (𝟙 T)) (hP : P ∈ torsionPoints E t N) :
    torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P hP ^ N = 1 :=
  let ⟨g, hgsplit⟩ := exists_pow_transitionUnitOfCover_split E hsm t N Q hQ M hM W e
  torsionSplittingEval_pow_eq_one_of_split E hsm t N Q hQ M hM W hW e hnorm P hP g hgsplit

/-! ## Bilinearity in `P` -/

/-- **(AP-D7, bilinearity in the first variable) — OPEN, `sorry`.** `h(P + P') = h(P) · h(P')`.

**Why it is true, and what blocks it.** Unlike multiplicativity in `Q`, this is *not* a statement
about the cocycle: the local values do not multiply pointwise, only their glued unit does. The
argument is translation invariance. For an `N`-torsion `P` let `τ_P` be translation by `P`, i.e.
the element `𝟙 + P ∘ π` of the group `(E.baseChange t).Point (E.baseChange t).π` of sections one
level up — the same "constants over the curve" device `WeilPairing/PoincareBiextension.lean` uses
for `β`, and the device `mulByN_zero` (`WeilPairing/KMPairing.lean`) already uses with `𝟙`. Then

* `τ_P ≫ [N] = [N]`, because `[N] ∘ τ_P = N • τ_P = 𝟙 + (N • P) ∘ π` and `N • P = 0`; hence
  `τ_P` preserves each open `[N]⁻¹(W i)`;
* therefore `τ_P^# h_i` again splits `f_{i,j} ∘ [N]`, so `τ_P^# h_i · π^#(h(P))⁻¹` is a
  *normalised* splitting of the same cocycle and `eq_of_normalized_splitting` gives
  `τ_P^# h_i = π^#(h(P)) · h_i`;
* evaluating at `P'` and using `P' ≫ τ_P = (P + P').1` gives the conclusion.

Every step is available except the transport in the first bullet: `τ_P ⁻¹ᵁ ([N]⁻¹ W i)` and
`[N]⁻¹(W i)` are equal only *propositionally*, via `congrArg (· ⁻¹ᵁ W i) (τ_P ≫ [N] = [N])`, and
`Γ(Y, -)` of that equality is a dependent rewrite across the whole statement. That transport, plus
the two `Point`-functoriality lemmas `π ≫ (N • P).1 = N • (π ≫ P.1)` and
`P' ≫ (X + Y).1 = (P' ≫ X.1) + (P' ≫ Y.1)`, is the whole of the missing work; none of it is
elliptic-curve geometry.

**Degenerate checks done.** At `N = 0` the statement is not vacuous — `torsionPoints E t 0 = ⊤` —
but it is true for a different reason: `[0]⁻¹(W i) = π⁻¹(0⁻¹ W i)` is the preimage of a base open,
so `AP-D2` (`eq_of_mem_sectionUnits`) forces `h_i = 1` and `h ≡ 1`. At `N = 1`,
`torsionPoints E t 1 = ⊥` and the statement is `torsionSplittingEval_zero`. -/
theorem torsionSplittingEval_add (P P' : (E.baseChange t).Point (𝟙 T))
    (hP : P ∈ torsionPoints E t N) (hP' : P' ∈ torsionPoints E t N) :
    torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm (P + P') (add_mem hP hP') =
      torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P hP *
        torsionSplittingEval E hsm t N Q hQ M hM W hW e hnorm P' hP' := by
  sorry

end Curve

end ModularCurves
