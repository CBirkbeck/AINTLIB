# Wedhorn vs Zavyalov for Tate Acyclicity (R2)

**Date:** 2026-04-08
**Reference:** Wedhorn lecture notes `1910.05934v1.pdf` §8 (pp. 81–85, 104–106) — full proof of Theorem 8.28(b) IS in the lecture notes (I missed it on first scan).
**Companion plans:** `2026-03-21-zavyalov-sheafiness.md`, `2026-04-08-zavyalov-decompleted-route.md`.

**Conclusion up front:** Wedhorn's proof is **dramatically more feasible** than Zavyalov's for our project. The R2 sorries should be reframed around Wedhorn's flatness/diagram-chase route, not around the v2 "Banach open mapping" framing. **The defect-correction / Banach OMP framing was the wrong tool**, but the topological embedding it was trying to prove is still part of the standard Wedhorn 8.26 definition we want — just achieved through a different route (universal-property identification with `A⟨X⟩/(closed ideal)`, which gives a topological iso).

**Update 2026-04-08 (Option A):** After audit, restored the topological embedding requirement to `IsSheafy` via a `Topology.IsEmbedding` field. The Wedhorn route still gives this — Phase 2 must produce Example 6.38 as a TOPOLOGICAL ring iso (universal property + Wedhorn Prop 6.17), and then the topological embedding is preserved through the diagram chase (Tate-algebra quotient maps are continuous and open).

---

## 1. The "topological embedding" — what it is and how to actually get it

**Wedhorn 8.26:** "sheafy" = `O_X` is a sheaf of TOPOLOGICAL rings. By
Remark 8.20 this requires the product restriction `O_X(U) → ∏ O_X(U_i)` to be
a TOPOLOGICAL EMBEDDING (injective + the source topology equals the subspace
topology from the product), not just an injection.

**The original v2 framing was:** "strict exactness of the Laurent row via Banach
open mapping → topological embedding". This was the wrong tool. The reviewer's
IsModuleTopology suggestion was a different wrong tool. Defect correction was a
third wrong tool.

**The right tool (Wedhorn's actual proof):** the topological embedding comes
from Example 6.38, which gives a TOPOLOGICAL ring iso `presheafValue D ≃_top
A⟨X⟩/(closed ideal)`. Once each side is identified with a Tate-algebra
quotient, the 3×3 diagram chase from Lemma 8.33 lives entirely in the world of
Tate-algebra quotients, where quotient maps are continuous and open and the
embedding property of the augmentation `A → A⟨ζ⟩/(f-ζ) × A⟨η⟩/(1-fη)` is
direct.

So R2 needs:
1. **R2-Phase2:** Example 6.38 as a TOPOLOGICAL ring iso (not just algebraic).
2. **R2b:** Lemma 8.33 in the Tate case, lifting the algebraic core
   `row3_exact` (already done) to the topological level via the iso from
   Phase 2.
3. **R2c:** Lemma 8.34 refinement transfer + assembly into `IsSheafy` instance.

The topological embedding is part of the goal, not a red herring. What WAS a
red herring: the specific route through "Banach open mapping on the completed
Laurent row". The right route is "universal property of `A⟨X⟩/(closed ideal)`
preserves topology automatically".

---

## 2. What Wedhorn's proof actually does

Wedhorn's lecture notes contain Theorem 8.28(b), Corollary 8.35, the supporting Lemmas 8.29–8.34, and the abstract Čech results in Appendix A. The proof for the strongly noetherian Tate case is on pp. 81–85; the abstract Čech machinery is on pp. 104–106.

The proof uses **only sheaf-of-abelian-groups** acyclicity (Definition A.1). Wedhorn's "F-acyclic" predicate is "the augmented Čech complex of abelian groups is exact" — exactly the same shape as our `IsSheafy.separation + IsSheafy.gluing` requirement, modulo cosmetic packaging.

**Definition A.1 (Wedhorn p. 105).** An open covering `U` of `X` is `F`-acyclic if the augmented Čech complex
```
0 → F(U) → Č^0(U,F) → Č^1(U,F) → Č^2(U,F) → …
```
of **abelian groups** is exact. **No topology mentioned.**

**Proposition A.4 (Wedhorn p. 106).** If a presheaf `F` is `U`-acyclic for every basic covering, then `F` is a sheaf and `Ȟ^q(U, F) → H^q(U, F)` is an iso for all `q ≥ 0`.

**Proof of Theorem 8.28(b) (Wedhorn p. 84).** "By Proposition A.4 it suffices to show that every open covering by rational subsets is `O_X`-acyclic. We may assume `A` complete. Every open covering of `X` has a refinement of the form `U_t := R(T/t)` for `T ⊆ A` generating `A` as an ideal (Lemma 7.54)… Thus by Proposition A.3(2) it suffices to show Lemma 8.34."

So Theorem 8.28(b) reduces to **abelian-group exactness of the Čech complex** for rational covers. No topology.

### The four algebraic ingredients

**Lemma 8.29 (technical preparation).** For a complete noetherian Tate ring `A` and finitely generated `A`-module `M`, the natural map `μ_M : M ⊗_A A⟨X⟩ → M⟨X⟩` is bijective. Proof uses the noetherian presentation `A^n → A^m → M → 0`, the 5-lemma, and Wedhorn Prop 6.18.

**Lemma 8.31 (key flatness lemma).** Let `A` be a noetherian complete Tate ring.
1. `A⟨X⟩` is faithfully flat over `A`.
2. For all `f ∈ A`, the rings `A⟨X⟩/(f-X)` and `A⟨X⟩/(1-fX)` are flat over `A`.

The proof of (2) is the cute one. To check `B := A⟨X⟩/(g) := A⟨X⟩/(f-X)` flat: by long exact Tor + flatness of `A⟨X⟩`, it suffices to show that for every f.g. `M`, multiplication-by-`(f-X)` `w_g : M⟨X⟩ → M⟨X⟩` is **injective**. Take `u = Σ m_ν X^ν` with `(f-X)·u = 0`:
- `f m_0 = 0`, `f m_ν = m_{ν-1}` for `ν ≥ 1` (the recursion `(+)`).
- Let `M' := ⟨m_ν⟩ ⊂ M`. By noetherianness, `M'` is f.g., say `M' = ⟨m_0, …, m_l⟩`.
- The recursion shows `M' = ⟨m_l⟩` (each `m_{ν-1} = f m_ν` is reachable from `m_ν`).
- `f^{l+1} m_l = 0` (by descending the recursion `l+1` times to `m_0`).
- Write `m_{2l+1} = a m_l`. Then `m_l = f^{l+1} m_{2l+1} = a f^{l+1} m_l = 0`. So `M' = 0`, so `u = 0`. ∎

**Corollary 8.32.** For a strongly noetherian Tate `A` and any finite cover by rational subsets `(U_i)`, `O_X(X) → ∏ O_X(U_i)` is **faithfully flat** (in particular injective). Direct corollary of 8.31 + Prop 8.30 (each `O_X(U_i)` flat over `O_X(X)`) + the covering condition translating to "no prime of `O_X(X)` is in the kernel of all restrictions".

**Lemma 8.33 (Laurent cover exactness).** For `f ∈ A`, `U_1 = R(f/1)`, `U_2 = R(1/f)`, the augmented Čech complex
```
0 → O_X(X) → O_X(U_1) × O_X(U_2) → O_X(U_1 ∩ U_2) → 0
```
is exact. Proof: a 3×3 diagram chase using Examples 6.38 & 6.39 to identify
- `O_X(U_1) = A⟨ζ⟩/(f-ζ)`,
- `O_X(U_2) = A⟨η⟩/(1-fη)`,
- `O_X(U_1 ∩ U_2) = A⟨ζ,ζ⁻¹⟩/(f-ζ)`.

**Lemma 8.34.** Every rational cover generated by `T ⊆ A` with `T·A = A` is `O_X`-acyclic. Proof uses 8.33 + induction over Laurent covers (`U_{f_1} × … × U_{f_r}`) + refinement-transfer Proposition A.3.

**Theorem 8.28(b).** Combine 8.34 + Lemma 7.54 (any rational cover refines to one generated by an ideal-generating `T`) + Prop A.4.

---

## 3. What we already have

| Wedhorn ingredient | Project file | Status |
|---|---|---|
| **Lemma 8.29** (`M ⊗ A⟨X⟩ ≃ M⟨X⟩` for f.g. `M`) | `TateAlgebra.lean` (not directly) | The 5-lemma argument is implicit in `tateAlgebra_flat`; could need extraction. |
| **Lemma 8.31(1)** (`A⟨X⟩` flat over `A`) | `TateAlgebra.lean:1705` `tateAlgebra_flat` | **DONE** (sorry-free, general noetherian Tate). |
| **Lemma 8.31(1)** faithful flatness | `TateAlgebra.lean:783` `faithfullyFlat` | **DONE for discrete only.** General case needs the prime extension `𝔭 ↦ {Σ a_ν X^ν : a_0 ∈ 𝔭}` — short proof, ~30 lines. |
| **Lemma 8.31(2)** (`A⟨X⟩/(f-X)` flat) | `TateAlgebra.lean:2591` `flat_quotient_fSubX_general` | **DONE** (sorry-free, general). Uses different proof route (saturated ideals + abstract flat-quotient engine) — gets the same conclusion. |
| **Lemma 8.31(2)** (`A⟨X⟩/(1-fX)` flat) | `TateAlgebra.lean:2601` `flat_quotient_oneSubfX_general` | **DONE** (sorry-free, general). |
| **Cor 8.32** (faithful flatness of product restriction) | `StructureSheaf.lean:887` `presheafValue_flat_of_tateQuotient` | **PARTIAL.** Has flatness conditional on TopologyComparison hypotheses; the assembly into faithful flatness of the product is not yet there. |
| **Lemma 8.33** (2-element Laurent cover exact) | `LaurentCoverExact.lean:193` `laurentCover_exact` (discrete), `:1560` `row3_exact` (general, with completion hypotheses) | **DONE algebraically** in both discrete and general cases. The general case takes `[UniformSpace A] [CompleteSpace A]` etc. — these match the strongly noetherian Tate setup. |
| **Lemma 8.34** (refinement transfer) | `CechCohomology.lean` + `LaurentRefinement.lean` | Refinement infrastructure exists. The exact statement of Lemma 8.34 (Laurent covers are acyclic, refinement transfers acyclicity) is partially assembled. |
| **Prop A.3** (refinement preserves acyclicity) | `CechCohomology.lean` `Refinement.cochainMap_*` | **DONE** for finite covers in our self-contained Čech complex. |
| **Prop A.4** (basis acyclicity → sheaf) | not in project | Standard sheaf theory; would need our `IsSheafy` class to be plugged into Mathlib's `Sheaf` framework, OR (much easier) we just prove our `IsSheafy` directly from the per-cover acyclicity. |
| **Lemma 7.54** (rational decomposition into ideal-generated covers) | `LaurentRefinement.lean:52` `rationalOpen_eq_iInter_singleton` | **DONE** (sorry-free). |
| **Example 6.38** (`presheafValue D ≃_top A⟨X⟩/(closed ideal)` for sno Tate) | `PresheafIdentification.lean:1419` `tateQuotientPresheafEquiv` (discrete only), `StructureSheaf.lean` (general, gated on TopologyComparison) | **DONE for discrete; gated for general.** This is the main missing piece. See §4. |

---

## 4. The single missing piece: Example 6.38 in the strongly noetherian Tate case

Wedhorn's proof of Lemma 8.33 (and the entire flatness route) relies on:

> **Example 6.38.** If `A` is a strongly noetherian Tate ring, `presheafValue D = A⟨T/s⟩` is **isomorphic as a topological ring** to `A⟨X⟩/(closed ideal generated by t - s·X)`.

The proof in Wedhorn (p. 55) is the **universal-property argument**:

> "By hypothesis, `C = A⟨X⟩` is noetherian and hence the ideal `𝔞 = (t - s·X)` is a closed ideal (Proposition 6.17). As `A` is a Tate ring, `T·A = A`. Hence the image of `s` in `C/𝔞` is a unit. Now it is easily seen that the homomorphisms `A → A⟨T/s⟩` and `A → C/𝔞` satisfy the same universal property."

So the proof has **three ingredients**:
1. **Proposition 6.17:** ideals in noetherian Tate rings are closed.
2. The image of `s` in `C/𝔞` is a unit (because `s ∈ T` and `T·A = A`).
3. **Both sides satisfy the same universal property** in the category of complete topological `A`-algebras with a designated unit `ι(s)` and power-bounded `t/s`.

**This is dramatically more tractable than:**
- Building up `IsModuleTopology A (A⟨ζ⟩)` from scratch
- Proving Banach open mapping for `presheafValue D`
- Building Proj + sheaf cohomology + Serre's finiteness for Zavyalov

In Lean, the universal-property route reduces to:
1. **Define the universal property** as a structure or predicate: "complete topological `A`-algebra `B` together with `ι : A → B` such that `ι(s)` is a unit and `{ι(t)/ι(s) : t ∈ T}` is power-bounded".
2. **Show `presheafValue D` has this universal property.** We essentially have this — the `presheafValue D` was defined precisely as the completion satisfying it. The relevant API is `extensionHom` and `restrictionMapAlg`'s factoring properties.
3. **Show `A⟨X⟩/(closed ideal)` has the same universal property.** Needs:
   - `(t - s·X)` is a closed ideal (use Proposition 6.17 — ideals in noetherian Tate rings are closed; we may already have this in `TateAlgebra.lean`).
   - The image of `s` in the quotient is a unit.
   - Universal property of `A⟨X⟩` (lifting `X` to a power-bounded element).
   - Universal property of the quotient by an ideal.
4. **Conclude `presheafValue D ≃+* A⟨X⟩/(closed ideal)`** as topological rings via uniqueness of the universal-property object.

We have most of the building blocks. The biggest single gap is **Proposition 6.17 in Lean**: "ideals in noetherian Tate rings are closed".

---

## 5. Comparison: Wedhorn vs Zavyalov

| Dimension | Wedhorn flatness route | Zavyalov decompleted-complex route |
|---|---|---|
| **Mathematical depth** | Algebraic; uses noetherian module theory + Tate algebra structure + universal properties | Algebro-geometric; uses Proj construction + sheaf cohomology + Serre's finiteness or FP-approximation |
| **Mathlib middle layer needed** | None — pure noetherian commutative algebra | Quasi-coherent sheaves, higher direct images, Serre's theorem (all absent from Mathlib) |
| **Main missing piece in our project** | Example 6.38 in the strongly noetherian Tate case (universal-property argument) | The entire algebraic-geometry middle layer |
| **Lines of new code estimate** | ~600–800 lines (Example 6.38 + Cor 8.32 assembly + Lemma 8.34 finalization + Prop A.4 connection) | ~3000–5000 lines (build sheaf cohomology theory, then port Zavyalov Steps 2–4) |
| **Risk** | Universal property argument is standard; we already have most building blocks. Main risk: getting the Tate algebra closed-ideal infrastructure right. | High: Mathlib gap is enormous; getting Serre's theorem in Lean is itself a separate research project. |
| **Topological embedding** | **Not needed** — Wedhorn's proof goes via sheaf-of-abelian-groups and our `IsSheafy` only requires sheaf-of-sets. | Not needed (Zavyalov also just needs sheaf-of-abelian-groups + Bourbaki strict-exact lemma for the topological side). |
| **Matches existing project structure** | **Yes** — TateAlgebra.lean, LaurentCoverExact.lean, Refinement, Lemma 7.54 are all already in place and oriented around this route. | No — would require new files for Proj/cohomology that don't exist. |

**Recommendation: pursue Wedhorn.** The amount of work to finish Wedhorn's route in Lean is comparable to a few sessions; Zavyalov's route is comparable to a multi-month sub-project (or never, without Mathlib growing).

---

## 6. Concrete plan for the Wedhorn route

### Phase 1 (1 session): Audit and reframe R2

1. **Update R2 (in `docs/TICKETS-axiom-clean.md`)** to drop the "strict exactness via Banach open mapping" framing. The new R2 is:
   - R2a: faithful flatness of product restriction (Cor 8.32).
   - R2b: 2-element Laurent cover acyclicity (Lemma 8.33), in the strongly noetherian Tate case.
   - R2c: refinement transfer + finalization (Lemma 8.34 + Prop A.4 connection).
2. **Delete the topological R2 sorries:** `defect_correction_exists`, `compatible_sections_in_image`, the topological-embedding-flavored docstring on `IsSheafy`. These were chasing the wrong problem.
3. **Rewrite `tateAcyclicity` Part 2 (gluing)** to use Cor 8.32 + Lemma 8.33 + refinement, instead of defect correction.

### Phase 2 (revised, 2026-04-08): Example 6.38 in the strongly noetherian Tate case

**Inventory (after session 1 of Phase 2):**

| Building block | File | Status |
|---|---|---|
| `pairSubring P : Subring (TateAlgebra A)` (= `A₀⟨X⟩`) | `TateAlgebraTopology.lean:193` | ✓ |
| `pairIdeal P : Ideal (pairSubring P)` (= `I·A₀⟨X⟩`) | `TateAlgebraTopology.lean:247` | ✓ |
| `pairSubring_isHuberRing` (`A₀⟨X⟩` as Huber ring) | `TateAlgebraTopology.lean:264` | ✓ |
| `pairIdeal_isAdic` (topology is `(pairIdeal)`-adic) | `TateAlgebraTopology.lean:287` | ✓ |
| `IsModuleTopology.isOpenMap_of_surjective_of_finite` (Prop 6.18(2)) | `NoetherianTateModules.lean` | ✓ |
| `Wedhorn.isClosed_ideal_of_noetherian` (Prop 6.17, ideal form) | `NoetherianTateModules.lean:299` | **STATED WITH SORRY** |
| Tate ring topology on `TateAlgebra A` ITSELF (not just subring) | — | ✗ **MISSING** |
| `CompleteSpace (TateAlgebra A)` with that topology | — | ✗ MISSING |
| `IsNoetherianRing (TateAlgebra A)` from `IsStronglyNoetherian A` | — | ✗ MISSING (for the general case) |
| `(1 - s·X)` closed in `TateAlgebra A` | — | ✗ MISSING |
| Continuous bijection `A⟨X⟩/(1-sX) → presheafValue D` | `TopologyComparison.lean` | **PARTIAL** (gated on wrong-topology hypotheses) |
| Topological iso via universal property | — | ✗ MISSING |

**Revised Phase 2 sub-tasks (estimated total ~800 lines over 3-4 sessions):**

**2.1 — Prop 6.17 statement.** Done 2026-04-08: `Wedhorn.isClosed_ideal_of_noetherian` stated as a sorry-theorem in `NoetherianTateModules.lean`. Proof deferred.

**2.2 — Natural Tate ring topology on `TateAlgebra A`** (~200 lines). Define a topology on `TateAlgebra A` such that `pairSubring P ⊂ TateAlgebra A` is an open subring with the existing `(pairIdeal)`-adic topology. Prove it makes `TateAlgebra A` a Huber ring with pair of definition `(pairSubring P, pairIdeal P)`, and a Tate ring when `A` has a topologically nilpotent unit. Completeness of `TateAlgebra A` follows from `A₀⟨X⟩` being I-adically complete (which itself follows from `MvPowerSeries` structure). T2 follows from the topology being Hausdorff (intersect of `I^n` is zero in `A₀⟨X⟩`).

**2.3 — Prop 6.17 proof** (~150 lines). Fill the `Wedhorn.isClosed_ideal_of_noetherian` sorry. Main tool: the quotient argument via Prop 6.18(1), where Prop 6.18(1) = "unique complete Hausdorff topology on f.g. modules". Mathlib's `IsModuleTopology` provides most of this; the remaining gap is showing `moduleTopology A M` is complete and Hausdorff for f.g. `M` over complete noetherian Tate `A`.

**2.4 — Apply Prop 6.17 to get `(1-sX)` closed** (~30 lines). Once 2.2 + 2.3 are done, applying `Wedhorn.isClosed_ideal_of_noetherian` to the ideal `oneSubfXIdeal D.s` is one line.

**2.5 — Quotient topology on `A⟨X⟩/(1-sX)` is complete + Hausdorff** (~50 lines). Quotient of complete by closed ideal is complete; quotient by closed ideal is T2.

**2.6 — `tateQuotientToPresheafHom` is a continuous bijection** (~200 lines). The existing `tateQuotientToPresheafHom D hb : A⟨X⟩/(1-sX) →+* presheafValue D` needs to be shown:
- Continuous (via `locTopology_continuous_lift` + `extensionHom` and the universal property of `presheafValue D`).
- Injective: `ker(tateEvalPresheafHom) = (1-sX)` in the Tate case. Uses the polynomial-division argument at the Tate-algebra level, combined with `(1-sX)` being closed (so the kernel equals the closure of `(1-sX)`, which is `(1-sX)` itself).
- Surjective: via density of `D.canonicalMap(Localization.Away D.s)` in `presheafValue D` + the image being closed (complete image into T2).

**2.7 — Banach → homeomorphism** (~50 lines). With 2.6 (continuous bijection between complete T2 topological rings) and Banach's theorem for Tate rings (Wedhorn Thm 6.16), conclude `tateQuotientToPresheafHom` is a homeomorphism — hence a **topological ring iso** `presheafValue D ≃_top A⟨X⟩/(1-sX)`. This completes Example 6.38.

**Estimated total for Phase 2:** ~680 lines across 3-4 sessions. The biggest single block is 2.2 (natural Tate topology on `TateAlgebra A`), which is pure infrastructure that unlocks everything else.

**Session 1 of Phase 2 (2026-04-08) completed:**
- Task 2.1 (Prop 6.17 statement)
- Inventory of existing building blocks
- Confirmation that the universal-property approach matches Wedhorn's Example 6.38 argument
- Identification of the key gap: the natural Tate topology on `TateAlgebra A` as a whole (we have it on the subring `pairSubring P` but not on the full ring).

### Phase 3 (1 session): Faithful flatness assembly (Cor 8.32)

1. **Wedhorn Prop 8.30**: combine `flat_quotient_fSubX_general` + `flat_quotient_oneSubfX_general` + the iso from Phase 2 to get `presheafValue D` flat over `A`.
2. **Cor 8.32**: assemble faithful flatness of the product restriction. The "no prime of `presheafValue C.base` lies in all kernels" step uses the Spa-point radical argument (which we have for the discrete case via `base_s_mem_annihilator_radical`; needs Tate-case version using Lemma 7.45).

### Phase 4 (1–2 sessions): Lemma 8.34 finalization + assembly

1. **Lemma 8.33 in the Tate case**: the 3×3 diagram chase. We have the algebraic core (`row3_exact`); need to lift via the topological iso from Phase 2.
2. **Lemma 8.34**: refinement transfer for Laurent covers. We have most of this in `Refinement.lean`.
3. **Theorem 8.28(b) assembly**: connect to our `IsSheafy` class.

### Phase 5 (1 session): Discharge old R2 sorries

1. Replace `defect_correction_exists`, `compatible_sections_in_image`, `restrictionMapHom_injective` with delegation to the new flatness/Wedhorn route.
2. Verify `lake build` passes.
3. Update `STATUS.md`, `TICKETS-axiom-clean.md`, `TICKETS-tate-acyclicity-v3.md`.

---

## 7. Effort estimate

| Phase | Lines (new) | Sessions | Risk |
|---|---|---|---|
| 1: Audit and reframe | ~50 (deletions) | 1 | Low |
| 2: Example 6.38 (Prop 6.17 + universal property) | ~400 | 1–2 | Medium (closed ideals in `A⟨X⟩`, universal property of quotient) |
| 3: Cor 8.32 assembly | ~150 | 1 | Low–Medium (Spa-point radical for Tate; existing infrastructure helps) |
| 4: Lemma 8.34 + assembly | ~150 | 1–2 | Low (we have the pieces) |
| 5: Discharge old sorries | ~50 | 1 | Low |
| **Total** | **~800** | **5–7** | |

Compare to Zavyalov: ~3000–5000 lines and indefinite risk on the algebraic-geometry middle layer. **Wedhorn wins by an order of magnitude.**

---

## 8. Open questions

1. **Is Proposition 6.17 in Mathlib?** "Ideals in noetherian Tate rings are closed" — should be derivable from Krull intersection. Worth one search before starting Phase 2.
2. **Do we already have the noetherian-domain version of Lemma 8.31(1) faithful flatness in our project?** I see it for `[DiscreteTopology]`. The general case is short (~30 lines).
3. **Is the universal-property argument for `A⟨X⟩/(closed ideal)` cleaner via "initial object in some category" or via a direct ring homomorphism + bijectivity construction?** Worth a small spike in Phase 2.
4. **For Cor 8.32 in the Tate case, do we need Lemma 7.45 (analytic point construction)?** We have it (`Lemma745.lean`). Need to verify it gives Spa points in the relevant rational opens.
5. **Should we update our `IsSheafy` docstring?** Currently misleading — claims topological embedding when the fields don't enforce it. The fix is one line.

---

## 9. Recommendation

**Pursue Wedhorn.** Concretely:

1. Start with **Phase 1 (audit and reframe)** in a single focused session. This includes correcting the misleading `IsSheafy` docstring.
2. Then **Phase 2 (Example 6.38 in the Tate case)**, which is the highest-leverage block of new work.
3. After that, the rest of the route is mostly assembly of pieces that already exist in the project.

The Zavyalov plan (`2026-04-08-zavyalov-decompleted-route.md`) should be **archived as "not pursued"** unless the Wedhorn route hits an unexpected wall in Phase 2. The single-axiom shortcut (Option C in that plan) remains available as a fallback.
