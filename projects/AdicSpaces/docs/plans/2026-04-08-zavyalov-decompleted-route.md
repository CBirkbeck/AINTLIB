# Plan: Zavyalov's Decompleted-Complex Route for Strictness (R2)

**Date:** 2026-04-08
**Target sorry:** R2 strict exactness of the Laurent row → unblocks
`defect_correction_exists`, `compatible_sections_in_image`, `restrictionMapHom_injective`,
`isSheafy_ofStronglyNoetherianTate_flat`.
**Reference:** Zavyalov, *Sheafiness of Strongly Rigid-Noetherian Huber Pairs*,
arXiv:2102.02776v2 (in `docs/2102.02776v2.pdf`), Theorem 3.5, Steps 2–4.
**Companion plan:** `docs/plans/2026-03-21-zavyalov-sheafiness.md` (full proof, written
March 21 before R2/R3/R4 refactoring; this plan is the focused tactical update).

---

## 0. Why this plan exists

Reviewer (2026-04-03) and follow-up ChatGPT consultation (2026-04-08) confirmed that
the right way to prove **strictness** of the completed Čech differentials in the
strongly noetherian Tate setting is **not** to attack the completed complex
directly with Banach open mapping. The right route is Zavyalov's: pass to the
**decompleted** complex `K^•` (rings of definition), prove openness of the
differentials *there*, then transfer back via Bourbaki [Bou98 III.2.12 Lemma 2].

Zavyalov's paper is for the more general strongly **rigid**-noetherian case, where
he must use the Fujiwara–Kato FP-approximation machinery (Appendix A) because
`A₀` is not noetherian — only "noetherian outside `V(I)`". For our project, our
hypothesis is `[IsNoetherianRing A]` (and hence `A₀` is noetherian whenever it
arises naturally), so **we can short-circuit Appendix A entirely** and use
classical EGA III machinery (Serre's finiteness, Artin–Rees, Krull intersection).

**The question this plan answers:** What does Zavyalov's proof actually need from
Mathlib, what's missing, and is this path realistic for our project?

---

## 1. Zavyalov's proof in 90 seconds

Setup. `(A, A⁺)` Huber pair, `A` strongly rigid-noetherian (we read: strongly
noetherian Tate). Pair of definition `(A₀, I)`. Standard cover
`X = ⋃_{i=0}^n X(f_0/f_i, …, f_n/f_i)` with `f_0·A + … + f_n·A = A`. Goal: the
augmented Čech complex `Č^•_aug(U, O_X)` is **exact with strict differentials**.

**Step 0.** WLOG `A` complete. (Spa(A,A⁺) ≅ Spa(Â,Â⁺) — Wedhorn 7.23.)

**Step 1 (reduction to standard covers).** Sheafiness ⇔ exact with strict `d` for
every covering ⇔ same for every standard covering of a rational subdomain
(Lemma 3.1 + Lemma 2.13 + Čech-to-derived ss). Replace the original covering by
a standard cover of `X` itself.

**Step 2 (decompletion + algebraic exactness).** Define
- `J := f_0·A_0 + f_1·A_0 + … + f_n·A_0` ⊂ `A` (an `A_0`-module, finitely generated)
- `S := Spec A_0`, `U := Spec A`
- `P := Proj ⊕_{m≥0} J^m`     -- "blowup of `Spec A_0` along the module `J`"
- `P' := Proj ⊕_{m≥0} (J·A)^m` -- since `J·A = A`, this is `Spec A` itself

The diagram
```
P' --p--> U          where p is iso (J·A = A),
|         |          j = (open immersion U ↪ S),
s         j          g = projection P → S projective,
v         v          s : U → P induced by s = g⁻¹ ∘ j,
P --g--> S            and j = g ∘ s (so s is affine since j affine, g separated).
```

So `R^i s_* O_U = 0` for `i > 0`, hence `H^i(P, s_* O_U) = H^i(U, O_U)` which
vanishes for `i > 0` (`U` affine), and `H^0 = A`. So the augmented Čech complex
of `s_* O_U` on `P` w.r.t. the affine cover `{D_+(f_i)}` is exact:
```
C^•_aug := (A[1] → C^•({D_+(f_i)}, s_* O_U))   exact in degrees ≥ -1.
```

The terms unwrap to
```
C^i_aug = ∏_{j_0<…<j_i} A[1/(f_{j_0}·…·f_{j_i})] = ∏_{j_0<…<j_i} A(F/f_{j_0};…;F/f_{j_i}).
```
After **completion** with the rational-localization topologies, we recover
`Č^•_aug(U, O_X)`. **Bourbaki [Bou98, III.2.12, Lemma 2]:** *the completion of an
exact-with-strict-differentials sequence is exact with strict differentials*.
So if we can prove `C^•_aug` is exact AND its differentials are **strict**
(i.e. open on the source's image), then so is the completed `Č^•_aug`. Done.

We already have exactness "for free" from the cohomology calculation. So we need
**strictness** of the decompleted differentials.

**Step 3 (reducing strictness to openness on the rings of definition).**
The natural map `O_P → s_* O_U` on the affine open
`D_+(f_{j_0}·…·f_{j_i})` is identified with
```
A_0[F/f_{j_0}; …; F/f_{j_i}]  →  A(F/f_{j_0}; …; F/f_{j_i}).
```
With the `I`-adic topology on the source, this is **injective, continuous, open**,
because the source IS a ring of definition of the target (`A_0[F/f_{j_0};…]` is
exactly the ring `D` from our Wedhorn setup, and `(I·D)`-adic topology = our
`locTopology`). So
```
Č^i_aug(P, O_P) ↪ C^i_aug   identifies the source as a ring of definition of C^i_aug.
```
(Mild care needed for `i = -1`: target is `A`, source is `H^0(P, O_P) ⊂ A`, and
we need this subring to carry the `I`-adic subspace topology. In the noetherian
case this is automatic — see Step 4 simplification below.)

So strictness of `d^i_C : C^i_aug → ker d^{i+1}_C` reduces to **openness** of
`δ^i : K^i → ker δ^{i+1}` where `K^• := Č^•_aug(P, O_P)` — the **decompleted**
complex. (Rings-of-definition are linked by `K^i ⊂ C^i_aug`, and openness on
either side transfers the other way via `{I^m K^i}`.)

**Step 4 (openness of `δ^i` via cohomology annihilation).** `δ^i` open ⇔ for
each `k`, there is `m` with
```
ker δ^{i+1} ∩ I^m K^{i+1} ⊂ δ^i(I^k K^i).                                   (*)
```
Unwrapping: this is the requirement that
```
H^{i+1}(P, I^m O_P) → H^{i+1}(P, I^k O_P)   is zero
```
for some `m` depending on `k` and `i ≥ 0`. By Theorem A.13 in Zavyalov, the
natural `I`-filtration topology on `H^{i+1}(P, I^k O_P)` equals the `I`-adic
topology, so it suffices to prove the cohomology is annihilated by some power
of `I`. This is **Claim 2** in Zavyalov: for any `i, k ≥ 0`, there exists `c`
with `I^c · H^{i+1}(P, I^k O_P) = 0`.

Proof of Claim 2:
1. `g : P → S` is quasi-compact and separated, so
   `R^{i+1}g_*(I^k O_P) ≃ \widetilde{H^{i+1}(P, I^k O_P)}`.
2. **Claim 1:** `g` is an isomorphism away from `V(I)`. (Because `J·A = A`, so
   `(A_0)_f → A_f` is iso for every `f ∈ I`, by [Hub93 Lemma 3.7].)
3. So `R^{i+1}g_*(I^k O_P) | (S \ V(I)) ≃ 0`. Combined with the fact that `I` is
   finitely generated, this gives `H^{i+1}(P, I^k O_P) = H^{i+1}(P, I^k O_P)[I^∞]`.
4. (Zavyalov's general case: `g` projective + Theorem A.5 + Lemma A.2 give that
   `[I^∞] = [I^c]` for some `c`.)
   **Noetherian shortcut (our case):** `A_0` noetherian + `g` projective ⇒
   `H^{i+1}(P, I^k O_P)` is a **finitely generated `A_0`-module** (Serre's theorem,
   EGA III.1.4.1). Finitely generated `+ I^∞`-torsion ⇒ annihilated by some `I^c`.

That closes Claim 2 and hence Step 4 and the whole proof.

---

## 2. Where the noetherian shortcut helps

| Zavyalov general case | Our noetherian case |
|---|---|
| `A_0` topologically universally rigid-noetherian | `A_0` noetherian (from `[IsNoetherianRing A]` + Eakin or by direct hypothesis) |
| FP-approximated sheaves (Appendix A) | Coherent sheaves |
| Theorem A.5: `H^i(X, F)` FP-approximated | Serre: `H^i(X, F)` finitely generated `A_0`-module |
| Theorem A.13: natural `I`-topology = `I`-adic | Artin–Rees / Krull intersection on f.g. modules |
| Lemma A.2: bounded `I^∞`-torsion via FP | Bounded `I^∞`-torsion via f.g. + noetherian |
| FK18 = Theorem 2.16 axiom | Not needed |

**The Appendix A axioms in the March 21 plan are unnecessary for us.** The whole
Step 4 collapses to: "f.g. `A_0`-module with `I^∞`-torsion ⇒ annihilated by some
`I^c`", which is a one-line consequence of noetherianness.

---

## 3. Mathlib infrastructure inventory

### What Mathlib has

| Component | Module | Notes |
|---|---|---|
| `AlgebraicGeometry.Proj` for graded rings | `AlgebraicGeometry.ProjectiveSpectrum.Scheme` | Object exists, basic properties |
| `Proj.IsSeparated` | `ProjectiveSpectrum.Proper` | Separatedness, properness pieces |
| `reesAlgebra I` | `RingTheory.ReesAlgebra` | Rees algebra of an *ideal* `I ⊆ R` |
| `AdicCompletion` | `RingTheory.AdicCompletion.*` | I-adic completion of modules and rings |
| `IsAffineHom` | `AlgebraicGeometry.Morphisms.Affine` | Affine morphisms predicate |
| `Ideal.adicTopology`, `Ideal.adicModuleTopology` | `Topology.Algebra.Nonarchimedean.AdicTopology` | I-adic topologies |
| `IsModuleTopology.isOpenMap_of_surjective` | `Topology.Algebra.Module.ModuleTopology` | Target needs `IsModuleTopology` only |
| `AddMonoidHom.isOpenMap_of_sigmaCompact` | `Topology.Algebra.Group.OpenMapping` | σ-compact source variant |
| Local Čech complex (in our project) | `Adic spaces/CechCohomology.lean` | Self-contained, finite cover, no scheme dep |
| Algebraic exactness of Laurent row (T1) | `Adic spaces/LaurentCoverExact.lean` | sorry-free, all degrees |

### What Mathlib does **not** have

| Missing piece | What it would take |
|---|---|
| **Quasi-coherent sheaves on schemes** (general) | Mathlib only has `Modules/Tilde.lean` (affine case). No general `IsQuasiCoherent` predicate, no QC categories. |
| **Higher direct images** `R^i f_*` | No `Mathlib.AlgebraicGeometry.Cohomology.*` directory at all. Sheaf cohomology of `O_X`-modules on schemes is absent. |
| **Serre's theorem** (`H^i(X, F)` f.g. for projective `X` over noetherian) | No coherent cohomology theory at all in Mathlib. |
| **Affine ⇒ higher pushforwards vanish** | `IsAffineHom` exists; the cohomological consequence does not. |
| **Bourbaki [Bou98 III.2.12 Lemma 2]** (completion of strict-exact = strict-exact) | Likely formalizable from existing completion API in `Topology.Algebra.GroupCompletion`, but I have not located it. |
| **Rees algebra of a *module* `J ⊂ A`** (not an ideal of `A_0`) | `reesAlgebra` is for `Ideal R`. We need `⊕ J^m` where `J ⊂ A` is an `A_0`-submodule with multiplication landing back in `A`. |
| **Proj of arbitrary graded `A_0`-algebras** (not just `A_0[X_0,…,X_n]/relations`) | `Proj` exists, but the specific graded algebra `⊕ J^m` would need to be packaged. |

**Bottom line:** Mathlib has the *bottom layer* (Proj as a scheme, structure sheaf on
Proj, rees algebra of an ideal) and the *top layer* (open mapping for module
topologies). The **middle layer** — sheaf cohomology of quasi-coherent modules,
higher direct images, Serre's finiteness — is completely absent. Zavyalov's proof
depends crucially on this middle layer.

---

## 4. Three options for actually closing R2

### Option A — Full Zavyalov port (proof of concept)

Build the missing middle layer in Mathlib-style, then port Zavyalov's Steps 2–4
verbatim (with the noetherian shortcut for Step 4).

**Required new files (~3000–5000 lines):**

1. `QuasiCoherentSheaf.lean` (~500 lines): predicate + basic API on the
   Modules side.
2. `SheafCohomology.lean` (~400 lines): cohomology of `O_X`-modules via Čech on
   affine covers; would need to thread through `CategoryTheory.Sites.SheafCohomology`.
3. `HigherDirectImage.lean` (~300 lines): `R^i f_*` for q-c morphisms; vanishing
   for affine morphisms.
4. `CoherentFiniteness.lean` (~600 lines): Serre's theorem (`H^i(X, F)` f.g. for
   projective `X` over noetherian `R`). This alone is most of EGA III.1.
5. `ReesModule.lean` (~200 lines): Rees algebra `⊕_{m≥0} J^m` for an `A_0`-submodule
   `J ⊂ A` such that `J^m ⊂ A` makes sense, plus `Proj` of it.
6. `BourbakiCompletionStrictExact.lean` (~200 lines): Bou98 III.2.12 Lemma 2.
7. `ZavyalovStrictness.lean` (~400 lines): Steps 2–4 of the proof itself.

**Risk:** sheaf cohomology in Lean is a known hard problem; Mathlib does not have
it for very good reason. Building it inside our project would be a multi-month
effort by itself. Even with full effort, the chance of getting Serre's finiteness
proved cleanly is low.

**Verdict:** Not realistic as a path to closing R2 in our project's lifetime.
This is Mathlib-scale work, not project-scale work.

### Option B — Axiomatize the middle layer, port Steps 2–4

Same as Option A but black-box the algebraic geometry inputs as `axiom`s:

```lean
axiom serre_finiteness :
  ∀ {R : Type*} [CommRing R] [IsNoetherianRing R]
    {n : ℕ} (M : ProjectiveSheafOver (Proj_n R)) [Coherent M] (i : ℕ),
  Module.Finite R (Hⁱ M)

axiom higher_direct_image_affine_vanishes : ...

axiom hub93_lemma_3_7 : ...
```

Then we would only need to formalize:
- The Proj construction `P = Proj ⊕ J^m` and its structure sheaf (using Mathlib's
  Proj) — needs Rees-of-module work.
- The diagram `P', P, U, S` and the maps.
- Step 3's identification of rings of definition (this part is mostly clean — it's
  the same `locSubring`-style argument we already have in `LocalizationTopology.lean`).
- Step 4's openness argument given annihilation.
- Bourbaki strict-exactness completion lemma (could try to prove from
  `UniformSpace.Completion` API).

**Effort:** ~1500–2000 lines new. ~5–8 axioms.

**Risk:** project hygiene concern — axioms are visible in `lean_verify` reports
and conflict with project's `mathlib-quality` discipline. Each axiom needs
maintenance and a discharge story.

**Verdict:** Possible but ugly. The axiom set includes Serre's theorem, which is
genuinely deep (months of formalization on its own). If we're going to axiomatize
this much, we might as well axiomatize the openness conclusion directly (Option C).

### Option C — Axiomatize Step 4's conclusion as a single theorem

Skip the algebro-geometric argument entirely and state the **conclusion** of
Zavyalov's Step 4 as an axiom with a clear citation:

```lean
/-- **Zavyalov 2102.02776 Step 4** (strictness of the decompleted Čech differentials).
For a strongly noetherian Tate ring `A` with pair of definition `(A_0, I)`, a
standard covering `{f_0, …, f_n}` with `Σ f_i A = A`, and the decompleted Čech
complex `K^• := Č^•_aug(P, O_P)` over `P = Proj ⊕ J^m` with `J = Σ f_i A_0`,
the differentials `δ^i : K^i → ker δ^{i+1}` are open. -/
axiom zavyalov_decompleted_strict : ...
```

Plus:

```lean
/-- **Bourbaki Bou98 III.2.12 Lemma 2.** Completion of an exact-with-strict-
differentials complex of complete topological groups is exact-with-strict-
differentials. -/
axiom bourbaki_completion_strict : ...
```

Then Wedhorn's textbook proof (which is the structure we already have in the
project) closes via these two axioms. The axioms have clean citations and can
be discharged later by porting Zavyalov OR by waiting for Mathlib to grow.

**Effort:** ~50 lines of axiom statement + ~300 lines connecting to the existing
Laurent infrastructure + R2 sorries discharged.

**Risk:** axioms remain in the build forever unless someone does Option A/B
later. But the axioms are *named* and *cited*, so the technical debt is visible.

**Verdict:** This is the **realistic short-term route**. It corresponds to
"axiomatize the deep math, code the easy bookkeeping". The discipline match is
similar to how `tate_aplus_le_A₀_sorry` and similar named-sorry helpers work
in the current R4 ticket.

### Option D (recommended) — IsModuleTopology lever, drop Zavyalov for now

After investigating, the **cleanest short-term route** does not actually go
through Zavyalov at all. The reviewer's first option (`IsModuleTopology` on the
target) would close `defect_correction_exists` directly **if** we can establish
`IsModuleTopology A (presheafValue D)`.

For strongly noetherian Tate rings, this should be true: each `presheafValue D`
is the completion of a localization `A[1/g]` whose topology is the `I`-adic
topology of a noetherian ring of definition. By Wedhorn Prop 6.18, the topology
on a finitely generated module over a noetherian Tate ring is unique
(= the module topology). The completed localization is a *Banach* `A`-module
in the strongly noetherian Tate setting, and "Banach module = module topology"
is the analytic version of Prop 6.18.

**The plan would be:**
1. Establish `IsModuleTopology A (A⟨ζ⟩)` for the free Tate algebra (one variable).
2. Transfer to the quotient `A⟨ζ⟩/(f-ζ) ≃_top presheafValue D` via a Mathlib
   `IsModuleTopology` quotient/iso lemma.
3. Apply `IsModuleTopology.isOpenMap_of_surjective` to `δ`. Source needs only
   `ContinuousAdd + ContinuousSMul`, both already inferred.
4. Strictness of `δ` follows. Then `ker δ` closed → complete → `ε` continuous
   bijection between completes → open by the same hammer (or by
   `AddMonoidHom.isOpenMap_of_sigmaCompact` since complete metrizable groups
   are σ-compact in our setting).

**Effort:** ~600 lines? The hard part is (1) — establishing `IsModuleTopology` for
`A⟨ζ⟩`. This requires proving the topology on `A⟨ζ⟩` is the finest making it a
topological `A`-module, which is a one-page argument in Wedhorn / Bosch but
requires the right Mathlib lemmas to be in place.

**Risk:** I don't yet know whether `IsModuleTopology` quotient/iso lemmas in
Mathlib are powerful enough to handle `A⟨ζ⟩/(closed ideal)` cleanly. Needs a
short investigation pass.

**Verdict:** **This is what I recommend exploring next**, before committing to
the Zavyalov port. Specifically: spend one focused session on
"can we get `IsModuleTopology A (A⟨ζ⟩)`?" If yes, R2 is solved cleanly. If no,
fall back to Option C.

---

## 5. Recommended next session

1. **Check `IsModuleTopology A (A⟨ζ⟩)` feasibility (1 session, exploratory).**
   - Search Mathlib for `IsModuleTopology` instances on `MvPolynomial`, power
     series, completions of polynomial algebras.
   - Look at how `IsModuleTopology.instProd` and `.iso` work in practice.
   - Try to write a stub `instance : IsModuleTopology A (A⟨ζ⟩) := …`.
   - **Decision point:** if the stub closes in <100 lines, pursue Option D;
     if it bottoms out on missing Mathlib API, switch to Option C.

2. **If Option D works:** plan a 3–4 session arc to:
   - Establish `IsModuleTopology A (A⟨ζ⟩)`
   - Transfer to `presheafValue D` via the quotient
   - Apply to `defect_correction_exists` and `compatible_sections_in_image`
   - Use to derive `restrictionMapHom_injective` (it falls out of strictness of
     the product restriction, which is the main R2 statement)

3. **If Option D fails:** introduce `axiom zavyalov_decompleted_strict` and
   `axiom bourbaki_completion_strict` as named axioms, citing this plan and the
   PDF location in `docs/`. Then close R2 via the existing Laurent infrastructure
   and treat the axioms as deferred work for a future Mathlib-scale push.

---

## 6. What this plan replaces / supplements

- **Supplements** `docs/plans/2026-03-21-zavyalov-sheafiness.md`: that plan
  treats the full proof; this plan focuses on the **strictness** chunk that R2 is
  blocked on, and reflects what we know about Mathlib gaps after a thorough check.
- **Updates** `docs/TICKETS-axiom-clean.md` R2 description: the "Banach OMP on
  completed row" framing is incorrect; the right framing is either
  "IsModuleTopology lever" (Option D) or "decompleted complex + axiomatized
  cohomology inputs" (Option C / Zavyalov).
- **Does not change** `docs/TICKETS-tate-acyclicity-v3.md` T1, T2, T3, T4 — those
  remain valid sub-pieces.

---

## 7. Open questions

1. Is `A⟨ζ⟩` in our project the same object as the free Tate algebra used in
   Mathlib (if any exists)? Likely no — we have a custom construction in
   `TateAlgebra.lean`.
2. Does the `IsModuleTopology` API include a quotient lemma that handles closed
   ideals cleanly, or only ideals where the quotient is f.g.?
3. Is there a Mathlib lemma matching Bourbaki [Bou98 III.2.12 Lemma 2] that I
   missed in the search? Worth one more pass through `UniformSpace.Completion`
   theorems.
4. The `i = -1` edge case in Step 3 needs care: the source is `H^0(P, O_P) ⊂ A`
   and we need this subring to be open with `I`-adic subspace topology. In the
   noetherian shortcut this is automatic from EGA-style arguments; in Lean we'd
   need to verify the corresponding `locSubring` carries the right topology.
   This is a check we already do in `LocalizationTopology.lean` and should
   transfer cleanly.
