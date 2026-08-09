# HANDOVER — ModularCurves, DS4 relative Weil pairing (2026-08-09)

Branch `dev/modular-curves` · worktree `/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves`
· HEAD at time of writing `b22304bc5` · `lake build ModularCurves` **green, 9771 jobs**.

This document is written to be the *only* thing an incoming worker has to read. It is deliberately
specific about what is **verified**, what is **claimed by a note in the tree** (and therefore
suspect), and what is **known-dead**.

---

## 0. Thirty-second version

The Katz–Mazur construction of the relative Weil pairing is **built end to end except for one
statement**:

| Open statement | File:line | Depth |
|---|---|---|
| `exists_torsionPoint_of_mem_kerMulByN` — AP-D4 `⊇` | `WeilPairing/KMPairing.lean:302` | deep — bottoms out in commutative algebra |

Everything else in the chain — `(★)`/`(★′)` self-adjointness of `[N]`, the relative theorem of the
square, AP-D4 `⊆`, AP-D5 existence *and* uniqueness, AP-D6 patching, AP-D7 `μ_N`-landing,
bilinearity in `Q` **and bilinearity in `P`** — is **proved and axiom-verified standard-three**
(`propext`, `Classical.choice`, `Quot.sound`). Re-verified today; see §4.

**AP-D7 closed on 2026-08-09**: `torsionSplittingEval_add` is proved, on the back of the new
`WeilPairing/Translation.lean`. Details and the route are in §5.1 — read it, because the same
`appLE`-based transport device is reusable and dissolves a class of dependent-open rewrites this
line kept hitting.

So the single remaining target is AP-D4 `⊇`, whose real bottom is §6 — and where the recorded route
may be a detour (**§6.3 is the most important paragraph in this document**).

---

## 1. Ground rules — non-negotiable, these are the project owner's

1. **Never** `set_option maxHeartbeats` or `set_option synthInstance.maxHeartbeats` on a proof.
   Hard rule. If a proof is slow, fix it structurally: local `haveI`/`letI` instances, extract a
   helper, drop wasteful type ascriptions. `backward.*` transparency options are allowed and are
   in fact the v4.33 bump-repair idiom (see §2).
2. **Never** put `2>/dev/null` next to a `lake` or `lean` command — a guardrail blocks the whole
   command. Use `2>&1`.
3. Push with `LEAN4_GUARDRAILS_BYPASS=1 git push origin dev/modular-curves`.
4. Guardrails also block `git reset --hard`, `git restore`, `git checkout --`, and **any git
   command containing the word "clean"** (in prose, write "axiom-verified" instead).
5. **Never `git add -A` while a subagent is mid-run.** It has swept scratch files into the repo
   twice. Stage explicit paths.
6. Temp/probe files go **only** in the session scratchpad, never under `projects/`.
7. Reference PDFs live in `refs/` and are **local only** — never committed, never pushed.
8. `#print axioms` at every milestone. `grep sorry` is not a substitute (§8.1).
9. You are a **PRODUCER** on a dev branch (see repo `CLAUDE.md`): prove theorems, leave `sorry`s
   where unfinished, reuse aggressively, and do **not** golf/restyle/dedup/bump — that is fleet
   work on `main`.

---

## 2. Build and tooling facts

```bash
cd /Users/mcu22seu/Documents/GitHub/aintlib-modular-curves
lake build ModularCurves            # ~9771 jobs; green today
```

- **`lake build ModularCurves` is also the duplicate/name-clash detector.** Run it *before* adding
  any new `import`. A conclusion-grep has twice missed a clash that this caught. Two shadowing
  incidents already cost real time (§9).
- **Some `ForMathlib/` modules are orphans** that `lake build ModularCurves` does not reach —
  build them explicitly by module name. `WeilPairing/Translation.lean` is currently one of these
  (not yet imported into `ModularCurves.lean`).
- The v4.33 bump idiom, when elaboration stalls: a file-level option triple including
  `set_option backward.defeqAttrib.useBackward true` and
  `backward.synthInstance.canonInstances false` / `respectTransparency.types false`. See
  `ForMathlib/LocalFlatnessCriterion.lean:58` for a live example. Whnf blowups want **opacity, not
  budget**.
- Lake's warning replay is partial across successive invocations — a second `lake build` may not
  re-emit every `declaration uses 'sorry'`. Trust a **from-scratch-ish** run, or `#print axioms`.

---

## 3. What the project is, and where DS4 sits

Goal (`.mathlib-quality/plan.md`): modular curves as representing objects of moduli problems of
elliptic curves, in the Katz–Mazur framework. Six strands; **DS4 is strand 2, the Weil pairing
`e_N : E[N] × E[N] → μ_N` over an arbitrary base.**

Design decision D7 (owner-confirmed): the final API is via Cartier duality/autoduality, with
**KM 2.8 norm/divisor as the comparison backend**, normalised to the Silverman convention
(`σζ = ζ^χ`, `det ρ_E = χ`). The route currently being built is that KM 2.8 backend.

Reference: Katz–Mazur, *Arithmetic Moduli of Elliptic Curves*, pp. 65–67 and pp. 88–89;
(2.8.1.7) and 2.6.2.1.

---

## 4. The Katz–Mazur construction — verified status

Re-verified today by `#print axioms`; all rows marked ✅ returned exactly
`[propext, Classical.choice, Quot.sound]`.

| Step | Declaration | File | State |
|---|---|---|---|
| (★) | `picMap_mulByHom_kappa_pow` | `Picard/SelfAdjointN.lean` | ✅ |
| (★′) | `picMap_mulByHom_kappa_eq_one` | `Picard/SelfAdjointN.lean` | ✅ |
| rel. thm of the square | `exists_invertible_tensor_idealModule_add` | `Picard/` | ✅ |
| — | `kappa_add` | `Picard/` | ✅ |
| AP-D4 `⊆` | `image_torsionPoints_subset_kerMulByN` | `WeilPairing/KMPairing.lean` | ✅ |
| AP-D4 `⊇` | `exists_torsionPoint_of_mem_kerMulByN` | `WeilPairing/KMPairing.lean:302` | ❌ **open** |
| AP-D5 existence | KM splitting `f_{i,j}∘[N] = h_i/h_j` | `WeilPairing/KMSplitting.lean` | ✅ |
| AP-D5 normalisation | every `h_i ∈ K_E^×` | `WeilPairing/KMNormalisation.lean` | ✅ |
| AP-D5 uniqueness | `eq_one_of_mem_kUnits`, `eq_of_div_mem_kUnits` | `WeilPairing/UnitSheaf.lean` | ✅ |
| AP-D6 | the `h_i ∘ P` patch to `h(P) ∈ Γ(S,𝒪_S^×)` | `WeilPairing/KMPatching.lean` | ✅ |
| AP-D5/D7 glue | `torsionSplittingEval` (the definition) | `WeilPairing/KMBilinear.lean` | ✅ |
| AP-D7 `μ_N` | `torsionSplittingEval_pow_eq_one` | `WeilPairing/KMBilinear.lean:307` | ✅ **unconditional** |
| AP-D7 bilinear in `Q` | (tensor-cocycle route) | `WeilPairing/TensorCocycle.lean` | ✅ |
| AP-D7 bilinear in `P` | `torsionSplittingEval_add` | `WeilPairing/KMBilinear.lean` | ✅ **closed 2026-08-09** |
| AP-D7 support | `eq_mul_globalTwist_of_translate`, `translateByPoint_comp_mulByN` | `WeilPairing/Translation.lean` | ✅ |

Module inventory (lines): `KMPairing` 394, `KMSplitting` 382, `KMUniqueness` 387, `KMNormalisation`
350, `KMBilinear` ~460, `KMPatching` 275, `TensorCocycle` 297, `UnitSheaf` 290,
`PoincareBiextension` 618, `Translation` 318.

Neither `Translation.lean` nor the new part of `KMBilinear.lean` contains a single `set_option` —
no heartbeat bumps, no transparency overrides. Keep it that way.

---

## 5. The two open statements

### 5.1 `torsionSplittingEval_add` — AP-D7, bilinearity in `P` — **CLOSED 2026-08-09**

> Retained because the device it introduced is reusable, and because the sorry's own docstring
> (still partly present in the file) enumerates four "missing" bricks that now all exist — a
> future reader must not be misled into rebuilding them.

```lean
theorem torsionSplittingEval_add (P P' : (E.baseChange t).Point (𝟙 T))
    (hP : P ∈ torsionPoints E t N) (hP' : P' ∈ torsionPoints E t N) :
    torsionSplittingEval … (P + P') (add_mem hP hP') =
      torsionSplittingEval … P hP * torsionSplittingEval … P' hP'
```
`WeilPairing/KMBilinear.lean:353`. KM p. 89.

**The maths.** Unlike multiplicativity in `Q`, this is *not* a statement about the cocycle — the
local values do not multiply pointwise, only the glued unit does. It is **translation invariance**:
for `N`-torsion `P`, translation `τ_P` satisfies `τ_P ≫ [N] = [N]`, so `τ_P` preserves each open
`[N]⁻¹(W i)`; hence `τ_P^# h_i` again splits `f_{i,j}∘[N]`, so `τ_P^# h_i · π^#(h(P))⁻¹` is a
*normalised* splitting of the same cocycle and `eq_of_normalized_splitting` gives
`τ_P^# h_i = π^#(h(P)) · h_i`. Evaluate at `P'` using `P' ≫ τ_P = (P + P').1`.

**How it was closed.** A new module carries the infrastructure:

`projects/ModularCurves/ModularCurves/WeilPairing/Translation.lean` (318 lines, 19 declarations,
sorry-free, axiom-verified standard-three, imported from `ModularCurves.lean:260`).

It supplies exactly the four bricks the sorry's own docstring had enumerated as missing — **all
four claims of absence were correct at the time, and all four are now discharged**:

- `unitPullback` / `unitPullback_congr` — pulls unit sections back through `Scheme.Hom.appLE`.
  **This dissolves the docstring's blocker 3**: the transported open `τ⁻¹ᵁ([N]⁻¹Wᵢ) = [N]⁻¹Wᵢ`
  holds only propositionally, but `appLE` absorbs the comparison into a `Prop` argument, so
  `subst` + proof irrelevance replaces every dependent rewrite. `globalTwist` is the special case
  `f = π, U = ⊤`; `sectionEval` is the special case `V = f⁻¹ᵁU`.
- `translateByPoint` — transports `EllipticCurve.translateBy`
  (`GroupScheme/TranslationBySection.lean`) into the `pullback E.π t` presentation, exactly as
  `mulByN` (`Picard/SelfAdjointN.lean`) transports `[N]`. Specs: `translateByPoint_comp_snd`,
  `comp_translateByPoint`, `translateByPoint_comp_mulByN` (**blockers 1 and 2**).
- `preimage_translateByPoint_mulByN` — the open-preimage transport.
- `eq_mul_globalTwist_of_translate` — the translation invariance itself, routed through
  `eq_of_normalized_splitting` (`WeilPairing/KMUniqueness.lean`).

**The reusable lesson.** Brick 3 — the dependent transport `τ_P⁻¹ᵁ([N]⁻¹Wᵢ) = [N]⁻¹Wᵢ`, which
holds only *propositionally* and whose `Γ(Y,−)` is a dependent rewrite across the whole statement —
was the one that looked worst on paper. It is dissolved entirely by **phrasing pullbacks through
`Scheme.Hom.appLE` rather than `Scheme.Hom.app`**: the comparison of `V` with `f⁻¹ᵁU` then sits in
a `Prop` argument, so two pullbacks along *equal* morphisms are equal by `subst` + proof
irrelevance regardless of how the two `≤` proofs were produced. **This line hits that shape
repeatedly; reach for `unitPullback`/`unitPullback_congr` before writing any dependent rewrite.**

### 5.2 `exists_torsionPoint_of_mem_kerMulByN` — AP-D4 `⊇`

```lean
theorem exists_torsionPoint_of_mem_kerMulByN (N : ℕ) (hN : N ≠ 0)
    (L : Scheme.Pic (pullback E.π t)) (hL : L ∈ kerMulByN E t N) :
    ∃ Q : (E.baseChange t).Point (𝟙 T), Q ∈ torsionPoints E t N ∧ kappa E hsm t Q = L
```
`WeilPairing/KMPairing.lean:302`. This is **Abel's theorem** in two halves:

1. **injectivity** — `IsKappaInjective E hsm t`, i.e. `κ(Q) = 1 → Q = 0`. Nothing in the tree
   proves it; `EllipticCurve/AbelEquivalence.lean` sets up the divisor↔section dictionary but never
   the rigidity `D_Q ∼ D_0 ⟹ Q = 0`.
2. **surjectivity onto `kerMulByN`** — for `L` in the kernel, `L ⊗ 𝒪(D_0)` is fibrewise of degree
   one, so `f_*(L ⊗ 𝒪(D_0))` is invertible by cohomology-and-base-change and the evaluation map
   cuts out a relative effective Cartier divisor of degree one; that divisor is `D_Q` for a unique
   section `Q` by **`exists_section_of_degree_one` (proved, axiom-clean)**, and `L = κ(Q)` after
   rigidifying.

Also silently needed: the fibre-degree bookkeeping `deg([N]^*L) = N²·deg L` on geometric fibres, so
that `[N]^*L = 1` and `N ≠ 0` give `deg L = 0`. **The tree has no fibrewise degree function on
`Pic`** — that has to be built.

`hN : N ≠ 0` is genuinely necessary: `kerMulByN E t 0 = picRel`, onto which `κ` is not surjective.

**Escape hatch already in place:** `exists_torsionPoint_of_mem_kerMulByN_of_surjective` is proved
and axiom-clean, and carries the two Abel halves as hypotheses. Consumers who want an axiom-clean
result should use that. Nothing in `KMPairing.lean` depends on the sorried version except
`kappa_image_torsionPoints_eq_kerMulByN`.

---

## 6. The real bottom: the AbelEquivalence chain

`EllipticCurve/AbelEquivalence.lean` has **four** sorries. Cite them carefully: the `theorem` line
and the `sorry` line differ, and the tree's own cross-references use the **`sorry`** line.

| decl @ | sorry @ | Declaration | Content |
|---|---|---|---|
| 836 | 848 | `evalGenerator_mem_nonZeroDivisors` | local generator of the vanishing ideal is a nonzerodivisor (KM p. 66) |
| 960 | 971 | `relEffCartierDiv_of_degreeOne_package` | **"Blocker 4"** — `IsIso ((sectionVanishingIdealSheaf M hM σ).subschemeι ≫ π)` |
| 981 | 994 | `exists_relEffCartierDiv_of_degreeOne` | `ℐ_D ≅ π^*(π_*M) ⊗ M⁻¹` (AP2-B2/B3 head) |
| 999 | 1013 | `relEffCartierDiv_degree_one_of_degreeOne` | the divisor has fibre degree one |

### 6.1 What is already proved around them (do not rebuild)

- `exists_section_of_degree_one` — **proved**. Given `[D.finite] [D.flat] [D.lfp]` and
  `∀ s, D.degree s = 1`, it gets `IsIso (D.ideal.subschemeι ≫ π)` from mathlib's
  **`Scheme.Hom.isIso_iff_finrank_eq`**, then builds the section as
  `inv (D.ideal.subschemeι ≫ π) ≫ D.ideal.subschemeι`.
- `relEffCartierDiv_of_isIso_subschemeι` — **proved**. `IsIso (I.subschemeι ≫ π) ⟹ ∃ D, D.ideal = I`
  (the three structural fields are `infer_instance` off `IsIso`).
- `degree_eq_one_iff_exists_section`, `degree_eq_one_of_ideal_eq_ker`,
  `exists_relEffCartierDiv_of_section`, `isInvertible_idealModule_of_section` — all **proved**.
- `mem_nonZeroDivisors_iff_injective_mulRight`,
  `mem_nonZeroDivisors_of_residueField_fibre_injective`,
  `mem_nonZeroDivisors_of_forall_maximal_residueField_fibre_injective` — all **proved**.

### 6.2 What Blocker 4 actually reduces to (verified today)

Because `exists_section_of_degree_one` and `relEffCartierDiv_of_isIso_subschemeι` are inverse to
each other, `IsIso` and `RelEffCartierDiv` are *equivalent* here — neither is free. **The genuine
content of Blocker 4 is: the vanishing subscheme `Z = V(σ)` is finite, flat and lfp over `S` with
fibre rank one.**

- *finiteness*: `Z` closed in `E`, `E → S` proper ⟹ `Z → S` proper; plus quasi-finite (each fibre
  `σ_s ≠ 0` on an integral curve) ⟹ finite. Needs `σ_s ≠ 0`, i.e. the package's base-change iso.
- *fibre rank one*: `σ_s` is a nonzero section of a degree-one bundle on a genus-one curve, so
  `div(σ_s)` is a single reduced rational point.
- *flatness*: **this is the whole difficulty**, and it is Stacks **00ME**.

### 6.3 ⚠️ The recorded route may be a detour — read this before planning

The board and the FOCUS file record that the route was **replaced after external review** with
*étale transversality* (`dh̄ ≠ 0` on the smooth fibre ⟹ `h : U → 𝔸¹_S` étale ⟹ `Z` finite étale of
degree one ⟹ iso; Stacks §37.38 / 055S, proving the special case from a standard-smooth Jacobian
presentation because the general slicing lemma routes through fibrewise flatness). That note also
correctly records that the *old* nonzerodivisor route **is** Stacks 00MF and does **not** dodge
Artin–Rees.

**However** — and this is the finding of the 2026-08-09 session — the tree's own architecture
points at a much smaller leaf, and it is fully sketched:

`ForMathlib/LocalFlatnessCriterion.lean` **already proves the whole of Stacks 00ME in the
`R`-substrate and `R`-free forms, sorry-free**:
`coker_flat_of_fibre_injective_forall`, `injective_of_lTensor_residueField_injective`,
`fibre_injective_of_maximal`, `coker_of_flat_of_fibre_injective`,
`injective_of_lTensor_residueField_injective_free`, `fibre_injective_of_maximal_free`,
`coker_of_flat_of_fibre_injective_free`.

The variant whose hypotheses actually match the geometry — `N` finite over the **upper** ring
`Γ(V)`, `M` flat over the **base** `R` — is `coker_of_flat_of_fibre_injective_sModule`. It had two
sorries. **Both were closed on 2026-08-09** (commits `12b5355a5` and `a5af3b7da`):
`ForMathlib/LocalFlatnessCriterion.lean` **is now entirely sorry-free, every declaration
axiom-verified standard-three.** Stacks 00ME is done in the form the geometry needs.

Two by-products are exported at root and are generally useful:

- `IsLocalRing.maximalIdeal_eq_map_of_surjective` — for a surjective local hom of local rings, the
  target's maximal ideal is the image of the source's. A genuine mathlib gap (loogle's only hit for
  the shape was `AdicCompletion.maximalIdeal_eq_map`).
- `Submodule.restrictScalars_map_smul_top` — `(J·S) • W = J • W` as sets, for **any** algebra map,
  no surjectivity. This is the device that lets a filtration argument over `R` be read in the ring
  over which the module is finite without transporting a single instance.

**The boarded route said "Artin–Rees". It is not needed.** The inductive step
`K ∩ 𝔪ⁿN ⊆ 𝔪ⁿ⁺¹N` is the usual associated-graded step, and it runs with *no graded machinery at
all*, because `N/𝔪N` is already a `k`-module and so `𝔪ⁿ ⊗[R] (N/𝔪N)` **is** the graded piece
`(𝔪ⁿ/𝔪ⁿ⁺¹) ⊗[k] (N/𝔪N)` on the nose. Writing `μ_P : I ⊗[R] P → P` for multiplication: lift
`x ∈ I•N` to `t`; `μ_M(lTensor I u  t) = u x = 0` and `μ_M` is injective *because `M` is flat*, so
`lTensor I u  t = 0`; naturality of `p ↦ 1 ⊗ p` moves this into the fibre; `lTensor k u` is an
injection of `k`-vector spaces hence **split**, and `lTensor I` of a split injection is injective —
which replaces the `cancelBaseChange`/flatness-over-`k` argument by a three-line retraction; finally
right-exactness of `⊗` puts `t` in the image of `I ⊗ 𝔪N`, whose `μ_N`-image is `(I·𝔪)•N`. Only the
second step uses flatness.

The docstring's plan for the base-change step said it needed the instance transport `S ↦ S ⧸ IS`.
**It did not.** Splitting the core into `injective_of_lTensor_residueField_injective_of_separated`
— which takes `hsep : ∀ x, (∀ n, x ∈ 𝔪ᴿⁿ • ⊤) → x = 0` in place of the whole `S`-package, that
being all the argument ever uses `S` for — reduces the base change to four steps that transport
nothing. That is a pattern worth remembering: **when a proof needs an instance package only to
supply one `Prop`, expose the `Prop`.**

**So the tool now exists. What is owed next is the wiring** — see the ⚠️ below.

**What I verified, precisely** (so you know where the risk is): I verified the four sorry
locations, the statements and proofs of `exists_section_of_degree_one` and
`relEffCartierDiv_of_isIso_subschemeι`, that the `R`-substrate/`_free` chains in
`LocalFlatnessCriterion.lean` are sorry-free, and that the `_sModule` chain's only gaps are the two
named above. This project's recorded routes have been wrong fifteen times (§10), so treat the rest
as a hypothesis.

**⚠️ Correction, established after the first draft of this document — read it.** A consumer grep
shows that **nothing in the tree consumes the `_sModule` chain at all**, and **nothing consumes
`evalGenerator_mem_nonZeroDivisors` either**. `relEffCartierDiv_of_degreeOne_package`'s proof body
is just

```lean
refine relEffCartierDiv_of_isIso_subschemeι (sectionVanishingIdealSheaf M hM σ) ?_
sorry
```

— it never calls `evalGenerator_mem_nonZeroDivisors`. So closing `:456`/`:473` **does not
automatically discharge anything**; it supplies a *tool* the fibrewise route needs, and the wiring
from that tool to `IsIso (Z ≫ π)` still has to be written. Concretely the remaining obligations
after the tool exists are: `IsFinite`, `Flat` and `LocallyOfFinitePresentation` instances for
`(sectionVanishingIdealSheaf M hM σ).subschemeι ≫ π`, plus `finrank = 1` at every point, which is
what `Scheme.Hom.isIso_iff_finrank_eq` consumes (see `exists_section_of_degree_one`'s proof for the
exact idiom). Budget for that wiring, not just for the commutative-algebra leaf.

Also note the warning already in the tree: the `_sModule` variant of the residue-field core "is
sorried and must not be used" — that comment sits next to `evalGenerator_mem_nonZeroDivisors` and
is *why* it is still open. Closing `:456`/`:473` removes that prohibition.

### 6.4 Hypothesis audit for Blocker 4 (do not weaken)

`h⁰ = 1` and `H¹ = 0` alone are **not** enough. Also needed: smooth geometrically integral
genus-one fibres, `deg M_s = 1`, and the base-change iso giving `σ_s ≠ 0`.

---

## 7. Dead ends — logged, do not revisit

1. **`ProjIsPrincipal` / `kappaDivisor_add_linEquiv` is UNSOUND over non-closed fields**
   (`.mathlib-quality/b2_log.jsonl`, ticket T10-asm): `projectiveDivisorOf` sees only `k`-rational
   points. It is no longer needed at all — the field-level theorem of the square is now proved by
   the explicit chord-and-vertical route.
2. **`WeilPairing/LineVertical.lean` is NOT about the chord and the vertical** despite its header.
   2350 lines with no Weierstrass polynomial, no `linePolynomial`, no `slope`, no `addX`. Two
   tickets were pointed at it on the strength of the header alone.
3. **"cover, generators and ratio must be produced together" was a WRONG DIAGNOSIS.** The unit is
   pinned by any ideal identity already in hand; absorbing it into one generator makes the ratios
   equal on the nose.
4. **Recovering the chord/vertical shape from the ideal identity alone is BLOCKED** — it needs the
   coordinate ring to be Dedekind. Split the call site instead.
5. **The μ_N / level-cover route for the pairing would have proved the pairing trivial.** Retired.
6. **Route β (descend the determinant model from a full-level cover)** is built end to end and
   axiom-verified but **unsourced and retired** — see `DEBT.md` `DS4-ROUTE-BETA`. Its top results
   are consumed nowhere. Dedup debt for `/cleanup` after merge, not producer work.
7. **The seesaw over a non-reduced base**: fibrewise-trivial ⟹ trivial is **false** over `k[ε]/(ε²)`.
   Prove on the universal (reduced) parameter space, then base-change down. Also: `0^*𝒪(D_0)` is the
   **normal** bundle, not the conormal.

---

## 8. Stale notes in the tree — verified stale today, do not trust

1. **`KMBilinear.lean:299–301`** says `torsionSplittingEval_pow_eq_one` "**Depends on `sorryAx`**,
   through `exists_pow_transitionUnitOfCover_split`". **False.** `exists_pow_transitionUnitOfCover_split`
   is proved at `KMBilinear.lean:281` and `#print axioms torsionSplittingEval_pow_eq_one` returns
   the standard three. Fix the docstring.
2. **`Picard/SelfAdjointN.lean:14`** says "One sorry left (`exists_invertible_tensor_idealModule_add`)".
   That leaf is closed; `SelfAdjointN.lean` is sorry-free.
3. **`tickets.md:38879`** warns that `picMap_mulByHom_kappa_eq_one` depends on `sorryAx` and tells
   you to bisect the chain. Stale — re-verified standard-three today.
4. **The AbelEquivalence sorry line numbers** in older board entries (836/960/994/1013) are stale;
   the current ones are 848/971/994/1013.
5. **`KMBilinear.lean`, `torsionSplittingEval_add`'s docstring** still opens
   "**— OPEN, `sorry`**" and carries a long "Precise inventory of what is missing" block naming
   four absent bricks. All four now exist in `WeilPairing/Translation.lean` and the theorem is
   proved. This is the single most misleading comment in the tree right now — fix it first.
6. General rule, learned the expensive way: **a docstring saying "blocked because mathlib lacks X"
   is a dated observation, not a fact.** Three such notes were false when acted on. Spend one
   search confirming X is still missing before planning around it. (Symmetrically: when a blocker
   *is* discharged, go back and rewrite the note — items 1–5 above are all failures to do that.)

### 8.1 `sorry` greps lie; `#print axioms` does not

`grep "by sorry\|:= sorry"` misses a bare `sorry`, and **zero file-sorries ≠ axiom-clean** —
inherited `sorryAx` is invisible to grep. Worse, **failed tactics inside structure fields and
`ext`-blocks become `sorryAx` with only a warning**. Grep `declaration uses` in build output *and*
run `#print axioms` at every milestone. Bisect blockers with `#print axioms`; they often sit in a
needlessly general lemma.

---

## 9. Coordinator / cleanup debt (not producer work, but it bites)

1. **`ModularCurves.idealModule`** (`EllipticCurve/PoleSheaf.lean:154`, the ideal module of a
   **morphism**) **shadows** `AlgebraicGeometry.Scheme.Modules.idealModule`
   (`Picard/IdealModule.lean:156`, of an **ideal sheaf**) inside `namespace ModularCurves`.
   Importing `ChartGroupSum` made 518 modules newly reachable and broke every bare `idealModule` in
   `SelfAdjointN.lean`. Worked around by one semantics-preserving line after `namespace ModularCurves`:
   `local notation "idealModule" => AlgebraicGeometry.Scheme.Modules.idealModule`.
   **Durable fix = rename `ModularCurves.idealModule`.**
2. `sectionVanishingIdeal` was the same failure mode and was silently orphaning the **entire**
   Seesaw line. Fixed (renamed to `sectionVanishingIdealSheaf`) — but that is why the board's older
   references use the old name.
3. `RelPicLocal.lean`: four primed theorems duplicate ~370 lines of the unprimed ones, which are
   now thin specialisations.
4. `isIso_idealGenHom`'s proof block is copy-pasted in three places.
5. `WeilPairing/TensorSection.lean` is a **dead module** whose `tensorSection` family
   full-name-collides with two other copies.
6. `WeilPairing/Basic.lean` (7 sorries) is the **old axiomatised pairing interface**, superseded by
   the KM construction. Candidate for deletion once `torsionSplittingEval` is wired through — the
   fleet will never touch it, because cleanup skips sorries by design.
7. `HasHighCechExactnessOpens` (arbitrary-base seesaw) is deliberately untouched: it quantifies
   over non-affine opens where the two-chart discharge does not reach. Reason is in its module
   docstring.

---

## 10. Standards that paid off — keep them

- **Verify fit by ELABORATION, not assertion.** Ship a scratchpad probe that applies the new result
  as a black box from an *independent* file. Seven consecutive passes did this and it repeatedly
  caught real mismatches. The last two added `fail_if_success` checks proving a gap was real, and
  tests over a **concrete non-reduced base**. That is now the expected standard.
  - Caveat learned: **de-guard your `fail_if_success` checks.** Three of them failed for the *wrong
    reason* — a dot-notation elaboration failure, a rename making the check vacuous, and a `whnf`
    timeout on a metavariable — and would have "proved" a gap that wasn't there.
- **Full `lake build ModularCurves` as the clash detector** before writing or importing.
- **Grep the CONCLUSION, not the inputs.** Finding all the ingredient lemmas is *not* evidence the
  target is absent. `fullLevelHom_baseChange` already existed while every ingredient grep missed
  it; `ForMathlib/BaseChangeKerCoker.lean` already had both halves of a hypothesis I re-derived
  from scratch. Before choosing a *route*, grep for that route's characteristic intermediate
  conclusion in the route's own vocabulary, and read the module docstrings of any directory that
  plausibly implements it — a route's home file is named after its machinery, never after the
  theorem it serves.
- **Boarded routes in this project have been wrong fifteen times** (thirteen over-engineered, twice
  the statement was actually **false**, once "missing API" already existed). The usual cause: the
  planner anchored on a nearby proved theorem's *shape* instead of reading what the statement
  needs. **Trust the statement over the sketch, and say so when you deviate.**

### Reusable by-products worth knowing about

`OverlapRel W b a j` (`b = a·tʲ` on the `Y ⊓ Z` overlap) with `.mul/.sub/.add/.pow/.cancel` and
base cases — the overlap dictionary this line has wanted for a long time; `germY`/`germZ` with
injectivity; `infChartOpen`; `projModelZero_ker_ideal_infChartOpen`;
`ker_ideal_of_fromSpec_factor` (replaces the whole `appLE` apparatus whose helpers are `private` in
`PoleFiltration.lean`); `isIso_idealGenHom`. Also: **mathlib's `XYIdeal_mul_XYIdeal` IS the
affine-chart theorem of the square.**

---

## 11. Recommended order of work

1. **Fix the stale docstrings** in §8 — cheap, and they have already misdirected work. In
   particular `KMBilinear.lean`'s `torsionSplittingEval_add` docstring still contains the long
   "Precise inventory of what is missing" block listing four bricks that now all exist; rewrite it
   to describe the proof instead of the obstruction, or a future reader will rebuild them.
2. **`evalGenerator_mem_nonZeroDivisors`** (`AbelEquivalence.lean:848`) — the first consumer of the
   now-complete Stacks 00ME. `ForMathlib/LocalFlatnessCriterion.lean` is sorry-free as of
   `a5af3b7da`, so the tool is available; nothing in the tree consumes it yet, so this is where the
   wiring starts. The neighbouring proved lemmas
   (`mem_nonZeroDivisors_iff_injective_mulRight`,
   `mem_nonZeroDivisors_of_forall_maximal_residueField_fibre_injective`) are the intended plumbing
   on the other side.
3. Then `relEffCartierDiv_of_degreeOne_package` (`:971`), `exists_relEffCartierDiv_of_degreeOne`
   (`:994`), `relEffCartierDiv_degree_one_of_degreeOne` (`:1013`).
4. Then the two Abel halves for AP-D4 `⊇` (§5.2), including the missing **fibrewise degree function
   on `Pic`**.
5. Then Group E — the DS4 register (`AP-E1`, `AP-E2…E6`) on the ticket board.
6. Housekeeping worth doing at some point: `WeilPairing/Translation.lean` is imported at
   `ModularCurves.lean:260`, out of the surrounding alphabetical order (between `KMUniqueness` and
   `LineVerticalAssembly`). Harmless, but move it when you next touch that block.

---

## 12. Wider project state (context, not your task)

80 sorry-bearing declarations are reachable from `ModularCurves.lean`. Concentration:

| Area | Count | Note |
|---|---|---|
| `GroupScheme/NIsogeny.lean` | 19 | pre-existing WIP |
| `LevelStructure/*` | 16 | `ExactOrder`, `Factorization`, `CartierDivisor`, `Basic` |
| `Moduli/*` | 15 | `GammaH`, `Coarse`, `EllCategory`, `SqrtCoverGlue`, `Stack`, … |
| `EllipticCurve/EndomorphismDegree.lean` | 7 | |
| `WeilPairing/Basic.lean` | 7 | superseded interface, see §9.6 |
| `ForMathlib/*` | 8 | incl. the two in §6.3 |
| rest | 8 | |

None of these except the `ForMathlib` pair and `AbelEquivalence.lean` are on the DS4 critical path.

---

## 13. Where the durable notes live

- `.mathlib-quality/tickets.md` — the dev ticket board (40 416 lines; grep, don't read).
- `.mathlib-quality/plan.md` — project goal, design decisions D1–D8, the DATA-SORRY REGISTER.
- `.mathlib-quality/plan-ds4-abel-pairing.md` — the DS4 route plan.
- `.mathlib-quality/plan-blockers-2026-08-08.md` — the blockers plan **plus an external review
  (ChatGPT 5.6 Sol) folded in as §"External review" (A1–A6)**, with self-corrections A2′/A2″/A2‴.
  Read this before re-planning Blocker 4.
- `.mathlib-quality/b2_log.jsonl` — statements found to be **mathematically wrong**. Check it
  before boarding anything; it is what stops a defective statement being re-ticketed.
- `.mathlib-quality/DEBT.md` — dead/unconsumed branches.
- `.mathlib-quality/beastmode_active` — the live FOCUS breadcrumb (mirrored at repo root
  `.mathlib-quality/beastmode_active`; **both copies must exist**).
