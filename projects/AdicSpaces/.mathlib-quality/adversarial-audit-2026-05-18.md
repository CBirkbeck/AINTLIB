# Adversarial decompose audit — acyclicity proof path

*Session 24, 2026-05-18. Goal: stress-test the IsSheafy proof path so when work starts, there are NO unexpected blockages.*

*Scope: critical path A3 → leaves only. Out-of-scope side branches are NOT audited.*

---

## The critical path (post Session-23 reviewer guidance)

```
A3  isSheafy_ofStronglyNoetherianTate                        [target]
│
├── EMBEDDING field                                          [Topology.IsEmbedding]
│   ├── INDUCING: B6  productRestrictionSub_isInducing_tate
│   │   ├── Lane C single-step closer (T273-T291)            ✓ done
│   │   └── F5  exists_*_clean (refinement tree, NO IsDomain) [SUSPECT]
│   │       ├── F7 first-stage Laurent (needs H2 finset Cor 7.32)
│   │       ├── F8 unit-generated cover → ratio Laurent
│   │       ├── F9 relative tree → absolute
│   │       └── F10 per-node transport
│   └── INJECTIVE: B7  tateAcyclicity_separation_via_cor832
│       └── C2  cor_8_32_clean (Wedhorn Cor 8.32)
│           ├── C1  prop_8_30_flat_clean (Wedhorn Prop 8.30)
│           │   ├── C4 presheafValue is Tate          (Ex 6.38, ✓ project)
│           │   ├── C5 presheafValue is noetherian    (Ex 6.38, ✓ project)
│           │   └── Wedhorn 8.31 (A⟨X⟩ flat)         [SEE RED-FLAG #1]
│           └── B5'  hSpa_surj_cover_level (Spec-surjectivity)
│               └── per-piece Spa-point construction at O(D)-level
│                   └── Wedhorn 7.45 chain at O(D)-level    [SEE RED-FLAG #2]
│
├── GLUING field
│   ├── B8  tateAcyclicity_gluing_via_descent
│   │   ├── C2  cor_8_32_clean (same as above)
│   │   ├── I1  Stacks 023N K.1.c (descent equaliser)
│   │   └── F12 tateAcyclicity Part 2 (LaurentRefinement)   [SEE RED-FLAG #3]
│
└── HasLocLiftPowerBounded typeclass instance
    ├── B1  hasLocLiftPowerBounded_of_stronglyNoetherianTate
    │   ├── C3  Spa(O(U)) ≃ rationalOpen(U)  (Wedhorn 8.2)  [API gap]
    │   ├── D8  power-bounded ↔ ∀ v, v(a) ≤ 1
    │   │   ├── D5 Wedhorn 7.41
    │   │   └── non-analytic argument via 7.40(5)
    │   └── completion-side power-boundedness at O(U)-level  [SEE RED-FLAG #4]
```

---

## RED FLAGS

### Red flag #1 — Wedhorn 8.31 in the project requires `[IsNoetherianRing P.A₀]`

**The project's `TateAlgebra.faithfullyFlat_general` and `flat_quotient_*` lemmas all take `(P : PairOfDefinition A) [IsNoetherianRing P.A₀]` as explicit hypotheses.**

- C1 (Wedhorn-clean Prop 8.30) is stated WITHOUT `(P, [IsNoetherianRing P.A₀])`.
- C1's body needs Wedhorn 8.31 either at the A-level or at the O_X(V)-level.
- At either level, the project's Wedhorn 8.31 requires noeth ring of def.
- Per expert review Q1, `[IsStronglyNoetherian A]` does NOT imply existence of a noeth ring of def (ℂ_p counterexample).

**Therefore C1 (Wedhorn-clean, no P) is unprovable using the project's current TateAlgebra wrappers.**

What needs to happen:

- **Option A**: Prove a weaker form of `TateAlgebra.faithfullyFlat_general` that needs only `[IsNoetherianRing A]` (and not `[IsNoetherianRing P.A₀]`). This is what Wedhorn 8.31 actually says in the literature ("Let A be a noetherian Tate ring"). The project's hypothesis profile is genuinely stronger than Wedhorn's.
- **Option B**: Add `(P : PairOfDefinition A) [IsNoetherianRing P.A₀]` to C1 (turning C1 into a parametric variant). Cascade upward to C2 and A3.
- **Option C**: Restrict the IsSheafy target to settings where a noeth ring of def is constructible (e.g., the BGR 5.2.6 height-1 field setting).

**Without one of these, work on C1 hard-stops the moment a worker tries to invoke `TateAlgebra.faithfullyFlat_general` and finds the hypothesis profile doesn't match.**

The Session-23 reply did not surface this. The reviewer's "Ex 6.38 → C1 → C2 → Lemma 8.34" route assumes Lemma 8.31 is available without noeth A_0 — but it isn't in the project, and it may not be in Wedhorn either (Wedhorn's proof on p.82 goes via the I-adic completion Â of A_0, which IS implicit use of A_0-structure but not explicit noeth-A_0 — needs careful reading).

**Action item**: audit the project's `TateAlgebra.faithfullyFlat_general` proof. Does it ACTUALLY require `[IsNoetherianRing P.A₀]`, or could the hypothesis be weakened to `[IsNoetherianRing A]` only? If the latter, the project's wrapper is over-tight and can be relaxed.

---

### Red flag #2 — `hSpa_surj_cover_level` (new B5) hits the same noeth-A_0 blocker

The reviewer prescribed: "direct Spa-point construction at the per-cover-piece level" for the new B5.

At the `presheafValue D`-level, this needs a Spa-point construction. Per Wedhorn 7.45, the construction uses a noetherian ring of definition for `presheafValue D`. But the same ℂ_p obstruction applies: strong noeth Tate of `presheafValue D` doesn't give noeth ring of def of `presheafValue D`.

**So the new B5 is in the same position as the old B5: provable parametrically but not unconditionally.**

What needs to happen:

- Same as Red Flag #1: either weaken Wedhorn 7.45's hypothesis profile, or accept that B5 needs noeth-A_0 hypothesis.

---

### Red flag #3 — Import-cycle for C2 / F12 is more serious than documented

- C2 (`cor_8_32_clean`) is in StructureSheaf.lean (upstream).
- The actual cover-level faithful flatness is `productRestriction_faithfullyFlat_tate_of_hSpa_points` in Cor832.lean (downstream).
- C2 has a `sorry` body with comment: "Cannot delegate to ... because that lives in Cor832.lean which imports this file (cycle)."

**The fix per reviewer's recommended route is to use** `hSpa_surj_cover_level` (the new B5) **as C2's Spec-surjectivity ingredient. But Cor832's existing combinator** `productRestriction_faithfullyFlat_tate_of_hSpa_points` **takes an `hSpa_points` hypothesis matching the OLD B5 shape (T, s, prime), not the new cover-level B5 shape.**

So even with the new B5 ready, C2 can't just delegate to the existing Cor832 combinator — that combinator needs to be refactored to consume the new cover-level shape. OR C2 needs a fresh combinator that doesn't go through Cor832 at all.

**Action item**: write a new combinator in Cor832.lean (downstream of StructureSheaf) that takes `hSpa_surj_cover_level`-shaped hypothesis + C1's flatness, and produces the faithful flatness. Then arrange for C2 to import and invoke it (via TateAcyclicityFinalAssembly.lean or similar).

This is real infrastructure work that the Session-23 reply did not surface.

---

### Red flag #4 — `A3` is missing `[CompleteSpace A]` in its signature

Wedhorn 8.28(b) is stated for **complete** strongly noetherian Tate affinoid rings. Wedhorn 8.31's proof on p.82 uses I-adic completeness of A_0. Wedhorn 8.30's proof reduces to V = X via Ex 6.38 + uses that A is complete.

The project's `IsTateRing A` typeclass extends `IsHuberRing A` extends `IsTopologicalRing A`. **Neither implies `CompleteSpace A`.** The A3 signature has only `[IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A] [NonarchimedeanRing A]` — **no completeness assumption**.

For incomplete Tate rings, the statements of Wedhorn 8.31 and 8.30 may not even hold. In particular, the project's `flat_quotient_fSubX_general` proof would fail on incomplete A.

**Therefore A3's signature is missing `[CompleteSpace A]`** (or equivalent: `[UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]`).

The Session-23 reviewer reply did not surface this. The reviewer's "Final Wedhorn-clean theorem path should use only: `[IsTateRing A] [IsStronglyNoetherian A] [T2Space A] [NonarchimedeanRing A]`" was wrong — completeness is genuinely needed and Wedhorn assumes it (the "complete" in "complete affinoid").

**Action item**: add `[UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]` to A3 (and B1, B5', B6, B7, B8, C1, C2 — every theorem on the Wedhorn-clean path). Update IsSheafy class definition if needed.

This is a SIGNATURE CHANGE cascading through every Wedhorn-clean theorem.

---

### Red flag #5 — F5 (non-domain refinement tree) is genuinely new mathematical content

Reviewer said: "F5 should be the final refinement-tree target. Wedhorn does not assume IsDomain. Refactor F4/F5 so the main theorem is non-domain."

The project's `RatioLaurentTree` construction uses non-zero-divisor data — the Laurent split of `R(T/s)` into `R(insert f T / s)` and `R(insert s (T) / f)` requires understanding when $sf - 0$ behaves invertibly. **In non-domain A (like $k\langle T,U\rangle/(TU)$), the Laurent split degenerates because $T \cdot U = 0$.**

How does Wedhorn handle this in the non-domain case? **The brief did not ask, and the reviewer did not specify.** Wedhorn's Lemma 8.34 proof on p.84 likely uses the structure of "topologically nilpotent unit + finite cover by f_i with f_i generating unit ideal" — none of which strictly require IsDomain. But the project's per-step Laurent split machinery does.

**Without a non-domain version of the Laurent split, F5 can't be discharged from the project's existing F7/F8/F9/F10 machinery (which all assume IsDomain via F4).**

**Action item**: investigate whether the project's Laurent-split machinery (F7-F10 and supporting) can be refactored to be non-domain-safe, OR whether Wedhorn's non-domain proof uses a fundamentally different decomposition.

This is the kind of work that needs reviewer guidance: "Here's how Wedhorn handles non-domain cases" or "you'll need a new decomposition technique X for this".

---

### Red flag #6 — F12 import-cycle scaffold is more than a routing issue

F12 (`tateAcyclicity` Part 2 in LaurentRefinement.lean) is sorry'd with the note "blocked by import cycle". The intended resolution: write a downstream wrapper in `TateAcyclicityFinalAssembly.lean` that combines Cor 8.32 + descent + refinement.

**That downstream wrapper doesn't exist yet.** The TateAcyclicityFinalAssembly.lean file has 0 sorries currently — meaning it doesn't even attempt the assembly. The N3/N4 cascade sorries in LaurentRefinement.lean are placeholders awaiting this downstream assembly.

**Action item**: write the assembly in TateAcyclicityFinalAssembly.lean. Substantial infrastructure: ~100+ LOC composing Cor 8.32 (when ready) + I1 (when ready) + refinement transfer.

---

### Red flag #7 — IsSheafy class typeclass already assumes `[HasLocLiftPowerBounded A]`

A3's signature doesn't have `[HasLocLiftPowerBounded A]` explicitly, but IsSheafy DOES require it (per the class definition). The instance B1 provides it via typeclass synthesis at compile-time.

**But B1's body is `sorry`. So at the point of stating A3 and checking that IsSheafy is well-formed, Lean accepts the instance synthesis — but the proof of B1 has not been done.**

This is a typeclass-trick. When A3 is finally proved (its body is no longer sorry), the proof transitively depends on B1's sorry. If B1 turns out to be unprovable in the strongly-noeth-Tate setting (Red Flag #2 cascade), then A3 effectively cannot be discharged.

**Action item**: B1 must be a real theorem before A3 can be closed. Currently it's blocked on either C3 (Spa-presheafValue equiv, API gap) or B5-style construction (which is itself flagged).

---

### Red flag #8 — D9 / D10 hypothesis profile is currently parametric but consumer sites expect non-parametric

D9 (Chevalley dominating valuation) and D10 (Wedhorn 7.45 lifted form) both currently take `(P : PairOfDefinition A) [IsAdicComplete P.I P.A_0]` (and arguably `[IsNoetherianRing P.A_0]`) explicitly. They are stated correctly as parametric.

**But their main consumer is B5'/B5 (Spa-point construction), and B5' (the new restated cover-level form) is stated WITHOUT P parameter.**

So D10 (parametric) cannot directly discharge B5' (no-P). Same Red Flag #1 / #2 issue.

**Action item**: either keep both parametric (with explicit P everywhere), or find a way to derive the P at the cover-piece level via Ex 6.38 (claimed to work but not yet verified for ring-of-def existence). Hidden infrastructure.

---

## Summary — what would actually be needed to discharge A3

Per the adversarial trace, the GENUINE infrastructure gaps are:

1. **Weaker `TateAlgebra.faithfullyFlat_general` with hypothesis `[IsNoetherianRing A]` only** (instead of `[IsNoetherianRing P.A₀]`). Unclear whether Wedhorn supports this; needs literature audit.

2. **Cover-level Spa-point construction theorem** (new B5') with a discharge route that doesn't require noeth A_0 at the cover-piece level.

3. **Completeness in A3 signature**: `[CompleteSpace A]` added.

4. **Non-domain refinement-tree machinery**: F5 + supporting F7-F10 refactored to be non-domain-safe.

5. **TateAcyclicityFinalAssembly.lean implementation**: the downstream wrapper that breaks the F12 / C2 import cycle.

6. **C1 and C2 either as parametric (with P) or via a Wedhorn-honest route that doesn't require noeth ring of def**.

7. **B1 instance proof** — currently sorry, transitively load-bearing.

8. **Decision on D9/D10**: keep parametric and accept that the no-P chain (A3, B5, etc.) is not directly dischargeable, OR find non-parametric variants.

---

## Net assessment

**A3 cannot be discharged with the current infrastructure** in the strongly-noeth-Tate-only setting. Multiple leaves are load-bearing on noeth-A_0 derivations that we've established are not constructible from `[IsStronglyNoetherian A]`.

The Session-23 reviewer was correct that A3 is **mathematically a theorem of Wedhorn** for complete strongly noeth Tate rings (with completeness restored to the signature). But the **proof route in Wedhorn implicitly uses the I-adic completion of A_0**, and that requires A_0 to have specific structure that strong noetherianity of A alone does not provide.

The project has two coherent paths forward:

### Path α — restore parametric `[IsNoetherianRing P.A₀]` to A3, C1, C2, B5

Effectively give up on A3 = "no P" and accept that the project's theorem is the PARAMETRIC variant. A1 / A2 already are this — A3 collapses to an alias of A1 minus IsDomain.

Pros: provable with existing infrastructure (TateAlgebra wrappers all take P).
Cons: weaker than Wedhorn-stated 8.28(b) (which doesn't have P explicit, though Wedhorn's proof secretly uses A_0).
Estimated work: cleanup pass + ~50 LOC.

### Path β — derive `[IsNoetherianRing P.A₀]` at the cover-piece level via Ex 6.38 + auxiliary

Use that Ex 6.38 says `presheafValue D` is again strongly noeth Tate. If we can additionally show "every strongly noeth Tate has SOME pair of definition with noeth ring of def" — wait, this is exactly B2/B3 which is FALSE.

So Path β requires a SECOND theorem: "the canonical pair of definition for `presheafValue D` constructed via Ex 6.38 has a noetherian ring of definition". This may be true for the SPECIFIC pair Ex 6.38 produces, even when not for arbitrary pairs.

**Action item — should be ASKED OF THE REVIEWER**: does Wedhorn's Example 6.38 produce a pair of definition for `O_X(V)` whose ring of definition is GUARANTEED to be noetherian (even when the original A's pair isn't)? If yes, Path β is unblocked. If no, Path α is the only honest path.

This is the kind of cascade question that should have been asked before. **Adding to the next expert-review brief if any.**

### Path γ — restrict project scope to BGR 5.2.6 setting

Restrict the target to "complete affinoid over a non-arch field of height 1". In this case the noeth ring of def is automatic. The downside is a much narrower theorem.

Estimated work: substantial restructure of typeclass profiles + scope reduction.

---

## Recommendation

**Defer A3 / B5' / C1-C2 (the no-P chain) until a third expert review answers**:
- Q-S24.1: Does the canonical pair-of-definition from Ex 6.38 have noeth ring of def, even when the original doesn't?
- Q-S24.2: Is Wedhorn 8.31 actually provable with `[IsNoetherianRing A]` only (no noeth A_0)?
- Q-S24.3: How does Wedhorn handle the non-domain case in Lemma 8.34?
- Q-S24.4: For the completeness gap — confirm A3 needs `[CompleteSpace A]` in the signature; should this be added or implicit-via-IsTateRing-strengthening?

**In the meantime, work on Path α**: restate A3 / C1 / C2 / B5' to take `(P : PairOfDefinition A) [IsNoetherianRing P.A₀]` parametrically. This collapses A3 to a clean alias of A1 (sans IsDomain, sans HasLocLiftPowerBounded). All downstream work then proceeds with existing infrastructure.

Estimated work for Path α completion:
- C1 parametric form: ~50 LOC (use existing chain)
- C2 parametric form: ~30 LOC (assemble from C1 + B5' cover-level)
- B5' parametric form: ~150 LOC (per-piece Spa-point with parametric P)
- B6 parametric form: 0 (Lane C closed) + F4 parametric (sorry, but pre-existing)
- B8 parametric form: ~80 LOC (I1 + descent + refinement transfer)
- I1: ~80 LOC (mathlib Flat.Equalizer infrastructure)
- F12 assembly: ~100 LOC in TateAcyclicityFinalAssembly.lean

**Estimated total Path α work: ~500 LOC** (vs. ~2400 LOC originally estimated for the no-P chain in Session 22, which is now revealed to be incomplete).

---

## Adversarial conclusion

The Session-23 reviewer's claim that "A3 is the real theorem; just retarget the proof" was **optimistic**. The actual retargeting requires either:

(a) infrastructure not in the project (weaker Wedhorn 8.31 with noeth-A-only),
(b) a reviewer-confirmed Ex 6.38 canonical-pair noetherianity fact (not asked),
(c) parametric restatement of A3 (acknowledging it's narrower than Wedhorn-stated 8.28(b)),
(d) restricted scope (BGR height-1 only).

**Recommended user decision**: pick (c) for the project's near-term ticket plan; ask reviewer about (b) as a possible future relaxation; don't start work on the no-P chain until (b) is confirmed or rejected.

This is exactly the kind of finding the "no unexpected blockages" goal of this audit was meant to surface — the prior reviewer's "keep A3 statement" advice glossed over the discharge-feasibility gap.
