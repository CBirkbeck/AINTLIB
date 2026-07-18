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

## Route-independent ALGEBRA FOUNDATION — LANDED (2026-07-08, axiom-clean)
The crux is no longer prose — it is a **named Lean predicate** `IsHopfGalois ρ`. The whole
route-independent algebra layer is built (4 new `ForMathlib/` files, all axiom-clean), so both the
general finite-flat route and the E[N] étale shortcut now aim at the *same* stated target:
- **`ComoduleCoinvariants.lean`** — `coinvariants ρ := AlgHom.equalizer ρ includeLeft`
  (`= B^{coρ}`), `mem_coinvariants`, `coinvariants_coaction` (`ρ s = s ⊗ 1` for `s ∈ S`). The
  mathlib-gap object (mathlib has only representation-coinvariants).
- **`Coaction.lean`** — `IsCoaction ρ` (counitality + coassociativity, the comodule-algebra axioms;
  mathlib has NO comodule class), element forms, `isCoaction_includeLeft` + `coinvariants_includeLeft = ⊤`
  (trivial-action validation).
- **`HopfGalois.lean`** — `canonicalGaloisMap ρ : B ⊗_S B →ₐ[S] B ⊗_R A`, `b ⊗ b' ↦ (b⊗1)·ρ(b')`
  (built as `Algebra.TensorProduct.lift` of `ρ`, `includeLeft` viewed over `S` — `ρ`'s `S`-linearity
  IS `coinvariants_coaction`); `canonicalGaloisMap_tmul`; **`IsHopfGalois ρ`** = `β` bijective +
  `FaithfullyFlat S B` (THE crux, stated); `IsHopfGalois.galoisEquiv` (the `B⊗_S B ≃ B⊗_R A` iso,
  the kernel-pair input).

**Reduction chain now fully mapped:** `IsHopfGalois ρ` ⟹ (023Q: `FaithfullyFlat` gives flat+surjective
`Spec B → Spec S`; `galoisEquiv` identifies the kernel pair with the groupoid) ⟹ affine-local
`IsColimit` of the `SpecEqualizer` cofork ⟹ (via `exists_unique_lift_of_isColimit` +
`isInvariant_iff_coequalizes`) the six `SubgroupQuotient` pins.

## FULL ROUTE-INDEPENDENT REDUCTION — COMPLETE (2026-07-08, axiom-clean)
`isColimit_of_isHopfGalois` is **PROVED** (`HopfGaloisQuotient.lean`): `(h : IsHopfGalois ρ) →
IsColimit (SpecEqualizer cofork)`, unconditional in `h`. The whole abstract chain
`IsHopfGalois ρ ⟹ affine-local IsColimit` is now axiom-clean, in three landed lemmas:
- **`isRegularEpi_specEqualizerπ`** (023Q half 1): `Module.FaithfullyFlat B^{coρ} B` → `π` regular epi
  (via `faithfullyFlat_algebraMap_iff` → `flat_and_surjective_SpecMap_iff` → `023Q`).
- **`isKernelPair_specEqualizerπ`** (023Q half 2): the cofork pair `(Spec ρ, Spec includeLeft)` is a
  kernel pair of `π` — tensor pushout `B ⊗_S B` → `Spec B ×_{Spec S} Spec B`
  (`isPullback_SpecMap_of_isPushout`), transported along `galoisEquiv`
  (`canonicalGaloisMap_comp_include{Right,Left}`, `IsPullback.of_iso`).
- **`isColimit_of_isHopfGalois`**: regular epi + kernel pair ⟹ `IsColimit` via
  `IsKernelPair.toCoequalizer'`.

**So the ENTIRE abstract Hopf-Galois → coequalizer reduction is DONE** (self-contained, upstreamable —
no E-specifics). Composed with `exists_unique_lift_of_isColimit` + `isInvariant_iff_coequalizes`, the
`SubgroupQuotient` pins follow *per affine chart* once `IsHopfGalois` holds there.

## Status / next — reduced to E-geometry + crux + glue
The abstract algebra + affine reduction is COMPLETE. Three obligations remain, all needing the actual
`E`-geometry (they connect the abstract `ρ`/`B⊗A` layer to the elliptic curve):
1. **`ρ = translation co-action` (3a-ii, E-geometry)** — identify the abstract `ρ : B →ₐ B ⊗ A` with
   `act^#` on a `G`-stable affine chart, under `O(G ×_S Spec B) ≅ B ⊗_R A` (`G` finite ⟹ affine over
   base). Bridges `IsCoaction`/`IsHopfGalois` to `translationAction`/`FiniteLocallyFreeSubgroup`.
2. **`IsHopfGalois (translation co-action)` (the crux PROOF, scoping-blocked v10.38)** — general
   finite-flat torsor theory vs. E[N] étale descent. p0 proceeds on the general crux per beastmode
   absent a redirect.
3. **glue (3a-iii/iv)** — G-stable affine cover + `SchemeQuotient` `GlueData`; assembles the per-chart
   affine quotients (from 1+2) into global `E/G`; discharges the six pins. Consumes 1+2.
