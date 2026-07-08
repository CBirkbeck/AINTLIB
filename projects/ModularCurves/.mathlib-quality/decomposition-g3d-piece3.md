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

## The construction reduces to a SINGLE deep crux (isRegularEpi refinement)
mathlib's `isRegularEpi_of_flat_of_surjective_of_isAffine` (`EffectiveEpi.lean`, `@[stacks 023Q]`)
says a **flat + surjective** map of affine schemes is a **regular epi = the coequalizer of its kernel
pair**. Apply it to the affine-local chart `Spec B → Spec B^{coG}`:
1. **`equalizer_val_comp` / `specMap_comp_specEqualizerπ` — DONE** (`ForMathlib/SpecEqualizer.lean`,
   axiom-clean): `Spec B → Spec(eq f g)` is a cofork of `Spec f, Spec g`. The affine local quotient
   *object* + cofork leg exist.
2. **kernel pair of `Spec B → Spec B^{coG}` `≅` `G ×_S Spec B`** — from freeness (`actPair_mono`, DONE)
   + the co-invariants structure; identifies the regular-epi's kernel pair with the local groupoid.
   Tractable once the affine chart is set up.
3. **THE CRUX — `B` is faithfully flat over `B^{coG}`** (`Spec B → Spec B^{coG}` flat + surjective).
   Then `023Q` gives the affine-local `IsColimit` **for free**, and `exists_unique_lift_of_isColimit`
   discharges the pins. This is the one genuinely hard, multi-week, mathlib-absent piece: it is the
   **torsor / Hopf-Galois property** "`E` is a `G`-torsor over `E/G`" (a free finite-locally-free action
   is faithfully flat onto its quotient). No shortcut; needs descent/torsor theory built from scratch.
4. **glue** the affine charts (`SchemeQuotient` `GlueData`); needs a `G`-stable affine cover
   (`E` projective ⟹ finite orbits in affine opens).

So: **everything is proven or tractable EXCEPT one crux — faithful flatness of `B` over `B^{coG}`
(the torsor property) — plus the glue.** That crux is the multi-week core.

## Status / next
Route DECIDED. Freeness DONE. Affine cofork DONE (`SpecEqualizer.lean`). The construction is now
pinned down to the **single deep crux (step 3: `B` faithfully flat over `B^{coG}`, the torsor
property)** + the glue. Both multi-week / mathlib-gap-filling; the crux needs finite-flat-group-scheme
torsor/descent theory from scratch. **Scoping decision boarded (v10.38): commit the multi-week general
Hopf-Galois crux, or take the linchpin-gated E[N] étale shortcut (T-Q5 + descent) for the rigidity
consumer.** Coordinator input welcome; p0 proceeds on the general crux per beastmode absent a redirect.
