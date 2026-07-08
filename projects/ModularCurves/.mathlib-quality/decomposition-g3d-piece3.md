# Worker decomposition — [T-G3d-infra] Piece 3: the coequalizer scheme `E/G`

*p0, 2026-07-08. Piece 3 of `decomposition-g3d-infra.md` — the one genuinely hard, scheme-theoretic
piece. Pieces 1 (interface), 2 (the `IsInvariant ⟺ coequalizer` bridge), 4 (factored map) are LANDED
and axiom-clean. This is the construction of the coequalizer scheme of `act, pr_E : G ×_S E ⇉ E`
(= `E/G`), after which all three interface pins read off mechanically through
`isInvariant_iff_coequalizes`.*

## What "build the scheme" buys, exactly
The bridge already did the hard categorical work. Concretely, once we have a scheme `Q`, a map
`π : E ⟶ Q`, and a proof `hπ : G.IsInvariant π` **that is universal** (every `G`-invariant `f` factors
uniquely through `π`), the pins are:
- `quotient := Q`, `quotientπ := π`, `quotientS := (the induced Q ⟶ S)`.
- `quotientπ_isInvariant := hπ` (directly, or `IsInvariant.of_coequalizes` from `π` coequalizing).
- `quotient_lift := the universal factoring` (its hypothesis `G.IsInvariant f` ⟹ `f` coequalizes via
  `IsInvariant.coequalizes` ⟹ factors).
- `quotientπ_over` from `quotientS`.

So the deliverable is precisely: **a universal coequalizer `π : E ⟶ Q` of `act, pr_E`** (with `Q ⟶ S`).

## Route DECIDED (recon complete, 2026-07-08)
The recon (`.mathlib-quality/` not committed) settled every question. Verdicts:
- **No turnkey scheme coequalizer / finite-flat-groupoid quotient in mathlib.** `Scheme` has only
  coproducts (`AlgebraicGeometry/Limits.lean`); no `HasCoequalizer`.
- **BUT the quotient PROPERTY is free once `Q` exists**: `AlgebraicGeometry/Sites/Fpqc.lean` gives
  `instance [Flat f] [Surjective f] [LocallyOfFinitePresentation f] : EffectiveEpi f` — an effective
  epi IS the coequalizer of its kernel pair. So a finite-locally-free `π : E ⟶ E/G` is automatically
  the universal coequalizer; its kernel pair is `G ×_S E` (via `actPair`, mono ⟹ the groupoid is an
  equivalence relation — **`actPair_mono` now PROVEN**). And `isRegularEpi_of_flat_of_surjective_of_isAffine`
  (`EffectiveEpi.lean`, `@[stacks 023Q]`) gives the same for the affine-local charts.
- **`AffineQuotient`/`SchemeQuotient` are CONSTANT-`[Group G]` only** — reusable *architecture*
  (`localQuotient → localQuotientMap` open-immersions → `tripleIso` cocycle → `Scheme.GlueData` →
  `quotient` + the `j`-relative descent keystone), NOT the affine engine.
- **`FixedPoints Bᴳ` must be replaced by Hopf-comodule co-invariants `{b : ρ b = b ⊗ 1}` — ABSENT
  from mathlib** (no `coinvariant`/`cotensor` in `RingTheory/{Coalgebra,Bialgebra,HopfAlgebra}`; the
  only near-hit is representation-coinvariants, the wrong object). **This is the one thing to build.**

**THE ROUTE (3a, confirmed):** affine co-invariants → glue, reusing the `SchemeQuotient` architecture.
- **3a-i (Hopf-comodule co-invariants, PURE ALGEBRA, the mathlib-gap core)**: for a comodule
  `ρ : B → B ⊗_R A` (`A = O_G`, a Hopf/bialgebra), the subalgebra `B^{coG} := {b : ρ b = b ⊗ 1}`, and
  the affine categorical quotient `Spec B ⟶ Spec B^{coG}` (flat+surjective ⟹ regular epi via `023Q`;
  universal property = comodule analogue of `existsUnique_invariantsπ_lift`). Self-contained; upstreamable.
- **3a-ii (co-action `ρ`)**: the translation co-action, affine-local dual of `translationAction`;
  `ρ = act^#` under `O(G ×_S Spec B) ≅ B ⊗_R A` (`G` finite ⟹ affine over the base).
- **3a-iii (G-stable affine cover)**: `E` projective over `S` ⟹ finite orbits lie in affine opens ⟹
  a `G`-stable affine cover exists (co-action analogue of `exists_isStableOpen_isAffineOpen`, which
  needs the affine diagonal / separatedness — `E.π` proper gives it).
- **3a-iv (glue)**: glue `Spec B^{coG}` on the `SchemeQuotient` `GlueData` skeleton; discharge the six
  `SubgroupQuotient` pins through `isInvariant_iff_coequalizes`. p2-stack-scale.
- **fppf route (3b)** stays GATED (representability of the fppf quotient sheaf needs SGA-III/ample per
  the board's T-E10 gate; `Sites/Representability.lean` would glue it but still needs the local charts
  from 3a-i). Do not take unless those land.

## Freeness — DONE (`actPair_mono`, axiom-clean, `TranslationAction.lean`)
`actPair = ⟨act, pr_E⟩` is a monomorphism (proven via `GrpObj.lift_left_mul_ext` right-cancelling the
common `pr_E` leg + `cancel_mono ιOver` + `hom_ext`; `ιOver` mono from `IsClosedImmersion ⟹ Mono`).
The action is free ⟹ the groupoid `G ×_S E ⇉ E` is an equivalence relation (the input to 3a's
effective-quotient existence) ⟹ the degree count `deg[N] = N² = rank E[N]` in `E/E[N] ≅ E`.

## Status / next
Route DECIDED. Freeness DONE. **Next leaf: 3a-i, the Hopf-comodule co-invariants affine quotient** —
pure algebra, the mathlib gap, self-contained, upstreamable; build as a new `ForMathlib` file mirroring
`FixedPoints.subalgebra`/`AffineQuotient` for co-invariants. Then 3a-ii/iii/iv. Multi-session
(p2-stack-scale); decompose 3a-i into leaves (comodule structure → coinvariants subalgebra → affine
universal property) when started.
