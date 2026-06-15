# Wedhorn 6.16 / 6.17 / 6.18 — Roadmap

**Goal**: Discharge the three "Proof. Missing" results in Wedhorn §6.3
("Banach's theorem for Tate rings") so the audit-pass-2 trio in
`StructureSheaf.lean` becomes genuinely sorry-free, and via the chain
`cor_8_32_clean → tateAcyclicity → isSheafy_ofStronglyNoetherianTate`,
the Wedhorn-exact form of Theorem 8.28(b) becomes provable.

## The three "Missing" results

### Wedhorn 6.16 = Banach's open mapping for Tate rings

> Let A be a topological ring that has a sequence converging to 0 consisting
> of units of A (e.g., if A is a Tate ring). Let M and N be Hausdorff
> topological A-modules that have countable fundamental systems of open
> neighborhoods of 0. Assume that M is complete. Let u: M → N be an A-linear
> map. Consider the following properties:
> (a) N is complete.
> (b) u is surjective.
> (c) u is open.
> Then any two of these properties imply the third.

### Wedhorn 6.17 = Noetherian iff every (sub)module closed

> Let A be a complete Tate ring, and let M be a complete topological
> A-module that has a countable fundamental system of open neighborhoods
> of 0. Then M is noetherian if and only if every submodule of M is closed.
> In particular A is noetherian if and only if every ideal is closed.

### Wedhorn 6.18 = Unique fg-module topology

> Let A be a complete noetherian Tate ring.
> (1) Every finitely generated A-module has a unique A-module topology that
>     is complete and that has a countable fundamental system of open
>     neighborhoods of 0.
> (2) Let f: M → N be an A-linear map of finitely generated modules that
>     are endowed with the topology from (1). Then f is continuous and the
>     map f: M → f(M) is open.

## Sources

### Wedhorn (arXiv:1910.05934)

- §6.3 "Banach's theorem for Tate rings", pp. 49-50
- All three results are stated with body "Proof. Missing"
- Cites [Hu1] (Bewertungsspektrum, German thesis) for foundational refs

### Huber [Hu3] (Math. Z. 217 (1994), 513-551)

- **Lemma 2.4(i)** = Wedhorn 6.16 (Banach's OMT for Tate-ring modules)
- **Lemma 2.4(ii)** = Wedhorn 6.18 (unique topology + strict maps for fg modules)
- *Huber's proof* (p.16 of [Hu3]):
  > "In order to prove (i) one can take over without any change the proof
  > of Banach's open mapping theorem (cf. **[B1, 1.3.3]**). (ii) follows
  > from (i) with the methods of **[BGR, 3.7]**."
- [B1] = Bourbaki, *Topologie Générale*, Ch. III §3 no. 3
- [BGR] = Bosch-Güntzer-Remmert, *Non-Archimedean Analysis* (Springer 1984)

### BGR §3.7 (pp. 163-167) — Banach algebras

**§3.7.2/1**: Let A be a k-Banach algebra and M a normed A-module such that
the completion M̂ is finite over A. Then M is complete (i.e. M = M̂).
- *Proof*: surjection π: A^n ↠ M̂ + Banach OMT ⇒ π open ⇒ M dense in M̂ + Nakayama ⇒ M = M̂.

**§3.7.2/2** (= **Wedhorn 6.17**): Let A be a k-Banach algebra and M a
complete normed A-module. Then M is Noetherian iff all submodules of M
are closed. In particular A is Noetherian iff all ideals in A are closed.
- *Proof*: Forward — Noetherian fg ideal closed by 3.7.2/1 (apply to image).
  Reverse — ascending chain of closed submodules; union M' is closed (=
  closure since chain stabilizes in closure), so Baire's theorem
  (Bourbaki [6] Ch 9 §5 Théorème 1) gives some M_i open in M', forcing
  M_i = M'.

**§3.7.3/1**: For 𝔐_A = "finite complete A-modules with continuous A-linear
maps" (A Noetherian k-Banach), every submodule M' of M ∈ 𝔐_A is closed.
- Direct from 3.7.2/2.

**§3.7.3/2** (= **Wedhorn 6.18(2)** continuity): Every A-linear map
φ: M → M' (M, M' ∈ 𝔐_A) is continuous.
- *Proof*: Choose epi π: A^n ↠ M. φ' := φ ∘ π is continuous (sum of
  A-linear coords). π open (Banach OMT). Hence φ = φ' ∘ π^{-1} continuous.

**§3.7.3/3** (= **Wedhorn 6.18(1)**): Each finite A-module M has a complete
A-module norm, and all such norms are equivalent.
- *Proof*: Existence via residue norm on A^n/ker π (ker closed by 3.7.2/2).
  Uniqueness via 3.7.3/2 applied to id_M between any two such topologies.

**§3.7.3/Cor 5** (= **Wedhorn 6.18(2)** openness): Each A-module hom
φ: M → M' (M, M' ∈ 𝔐_A) is **strict** (= image with subspace topology
equals quotient topology).
- *Proof*: BGR 3.7.3/Prop 4 — continuous k-linear φ: X → Y between Banach
  spaces is strict iff φ(X) is closed in Y. Image of φ is fg ⇒ closed.

## Bourbaki [B1] 1.3.3 = the underlying mathlib gap

The classical Banach OMT for **complete metrizable topological abelian
groups**:

> Let G, H be Hausdorff topological abelian groups whose topologies are
> defined by countable fundamental systems of neighborhoods of 0. Assume
> G is complete. Let f: G → H be a continuous group homomorphism. Then
> f is open iff f(G) is non-meagre in H. In particular, if f is
> surjective and H is complete, then f is open.

This is **Bourbaki Topologie Générale Ch. III §3 no. 3 Théorème 1** (modulo
mild restatements). The proof is the standard Banach argument:

1. Source G is BaireSpace (have it via mathlib instance
   `BaireSpace.of_pseudoEMetricSpace_completeSpace`).
2. For each n, `f(n·U) = n·f(U)` covers H by countable union (any nbhd U).
3. H Baire ⇒ some `n·f(U)` has nonempty interior ⇒ `f(U)` has nonempty
   interior ⇒ contains nbhd V of some point ⇒ `f(U − U)` contains nbhd of 0.
4. Iterate: f(U) ⊇ (1/2) f(U − U) ⊇ ... ⇒ Cauchy completeness of G + closure
   of difference structure ⇒ f(U) ⊇ small nbhd of 0.
5. Translation invariance ⇒ open everywhere.

### Mathlib status

| Result                                          | Status in mathlib (4.29.0-rc3)                                        |
|-------------------------------------------------|-----------------------------------------------------------------------|
| Banach OMT for normed spaces over normed field  | ✓ `ContinuousLinearMap` in `Mathlib.Analysis.Normed.Operator.Banach`  |
| Group OMT for σ-compact source                  | ✓ `MonoidHom.isOpenMap_of_sigmaCompact` in `Topology.Algebra.Group.OpenMapping` |
| BaireSpace from CompleteSpace + countable uniformity | ✓ `BaireSpace.of_pseudoEMetricSpace_completeSpace` in `Topology.Baire.CompleteMetrizable` |
| BaireSpace from T2 + LocallyCompact             | ✓ `BaireSpace.of_t2Space_locallyCompactSpace`                         |
| **Banach OMT for complete metric topological abelian groups** | **✗ MISSING — the Bourbaki [B1] 1.3.3 version**         |
| Nakayama's lemma                                | ✓ in `RingTheory.Nakayama`                                            |
| Baire's category theorem (closed sets)          | ✓ `nonempty_interior_of_iUnion_of_closed`                             |

The single missing piece is the **complete-metric-group OMT**.

## Layered ticket plan

### Layer 1: Mathlib gap (Banach OMT for complete metric topological groups)

**Ticket [T-BANACH-OMT-GROUP]**

```lean
theorem AddMonoidHom.isOpenMap_of_completeSpace
    {G H : Type*}
    [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [UniformSpace G] [CompleteSpace G] [(uniformity G).IsCountablyGenerated]
    [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    [UniformSpace H] [CompleteSpace H] [(uniformity H).IsCountablyGenerated]
    [T2Space H]
    (f : G →+ H) (hf : Continuous f) (hsurj : Function.Surjective f) :
    IsOpenMap f
```

**Proof sketch**: Steps 1-5 of the Bourbaki proof above. Estimated ~200-300
lines of Lean. The Cauchy step (4) is the most delicate — adapts to
complete uniform spaces via `CauchySeq.tendsto_of_completeSpace`.

**Mathlib lemmas needed**:
- `BaireSpace.of_pseudoEMetricSpace_completeSpace` (gives source Baire)
- `Filter.HasBasis.mem_iff`, `nhds.hasBasis_of_isCountablyGenerated`
- `nonempty_interior_of_iUnion_of_closed`
- `CauchySeq.tendsto_of_completeSpace`
- Translation lemmas: `IsOpen.preimage`, `IsTopologicalAddGroup.continuous_neg`, etc.

**Could be upstreamed to mathlib** as
`Mathlib.Topology.Algebra.Group.OpenMappingCompleteMetric`.

### Layer 2: Wedhorn 6.16 = T-BANACH-OMT-GROUP specialized to A-modules

**Ticket [T-WEDHORN-616]**

Direct corollary: if M, N are topological A-modules with countable nbhd
basis at 0, both complete + Hausdorff, and u: M → N is continuous
surjective A-linear, then u open. Body: just `f.toAddMonoidHom` +
T-BANACH-OMT-GROUP. ~20 lines.

### Layer 3: Wedhorn 6.17 = BGR 3.7.2/2

**Ticket [T-WEDHORN-617]**

For A complete Tate noetherian, M complete topological A-module with
countable nbhd basis at 0: M Noetherian iff every submodule closed.

**Proof sketch** (BGR 3.7.2/2):
- Forward (Noetherian ⇒ all submodules closed): every submodule M' ⊂ M is
  fg, take A^n ↠ M'. By T-WEDHORN-616 (applied to the inclusion of M̂'
  into M' if needed)... actually the cleaner route is via 3.7.2/1: if M̂
  is fg, then M = M̂. Apply to submodule = M̂'.
- Reverse (all submodules closed ⇒ Noetherian): ascending chain M_1 ⊂ M_2 ⊂ …
  Union M' is closed submodule. Then M' = ⋃ M_i is a countable union of
  closed sets in itself. By Baire on M' (complete metrizable), some M_i
  has nonempty interior, hence M_i ⊇ nbhd of 0 in M', hence M_i = M'.

**Mathlib lemmas needed**:
- T-WEDHORN-616 (Layer 2)
- `Baire.nonempty_interior_of_iUnion_of_closed`
- `IsOpen.zero_mem` style nbhd lemmas

~150-200 lines.

### Layer 4: Wedhorn 6.18 = BGR 3.7.3/2 + 3.7.3/3

**Tickets [T-WEDHORN-618-UNIQUE], [T-WEDHORN-618-CONT-OPEN]**

For A complete noetherian Tate:
- (1) [T-WEDHORN-618-UNIQUE]: every fg A-module M has a complete countably-
  generated A-module topology, unique up to homeo.
  - Existence: M ≅ A^n / K (K closed by T-WEDHORN-617 on A^n), quotient
    topology is complete (Hausdorff quotient of complete).
  - Uniqueness: id_M between any two such topologies is continuous (since
    A-linear and target has countable basis) + open (T-WEDHORN-616).
- (2) [T-WEDHORN-618-CONT-OPEN]: every A-linear φ: M → N (M, N fg with
  topology from (1)) is continuous + open onto image.
  - Continuous: via lift to A^n → N where A^n → N is sum-of-coords, continuous.
  - Open onto image: image is fg ⇒ closed by T-WEDHORN-617; image with
    subspace = quotient by T-WEDHORN-616.

~200 lines combined.

### Layer 5: Apply to the audit-pass-2 trio

**Ticket [T-AUDIT-PASS-2-STRONG-NOETH]** (= `isStronglyNoetherian_of_isNoetherianRing_isTateRing`)

For A noetherian Tate + complete (T2 + NonarchimedeanRing in the project
hypothesis): A⟨X_1,…,X_n⟩ noetherian for all n.
- Base case n=0: A itself, given.
- Inductive step: A⟨X⟩ = adic completion of A[X] along I·A[X], where I is
  the ideal of definition (of any principal pair).
- Mathlib gap **T-MATHLIB-STACKS-00MA** (ticket #36): adic completion of
  noetherian is noetherian (Stacks 00MA).
- Together with Hilbert basis (polynomial ring noetherian preserved), gives
  A⟨X⟩ noetherian.

**Ticket [T-AUDIT-PASS-2-A₀-NOETH]** (= `isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate`)

For A strongly noetherian Tate, the principal pair `IsTateRing.principalPair A`
has noetherian A₀. Uses T-WEDHORN-618 + standard descent.

**Ticket [T-AUDIT-PASS-2-SPA-POINTS]** (= `exists_hSpa_points_global_of_stronglyNoetherianTate`)

Spa-point existence at any prime: open case via trivial valuation
(already done), non-open case via Wedhorn 7.45 noetherian-ring-of-
definition variant (Wedhorn proves this case, no "Missing").
Needs A₀ noetherian from T-AUDIT-PASS-2-A₀-NOETH.

### Layer 6: Final cor_8_32_clean discharge

Once Layers 1-5 land, the audit-clean wrappers in StructureSheaf.lean
(currently sorry'd due to cycle blocker) discharge via:
1. Move to new file `Adic spaces/AuditCleanWrappers.lean` downstream of
   Cor832.lean (no cycle).
2. Use the audit-pass-2 trio to derive the per-pair hypotheses needed by
   `productRestriction_faithfullyFlat_tate_of_hSpa_points`.
3. Compose.

## Effort summary

| Layer                                | Estimated LOC  | Mathlib-upstreamable? |
|--------------------------------------|----------------|------------------------|
| Layer 1: complete-metric-group OMT   | ~250           | YES (clean upstream)   |
| Layer 2: Wedhorn 6.16 (A-module)     | ~20            | (project-local)        |
| Layer 3: Wedhorn 6.17                | ~150           | (project-local)        |
| Layer 4: Wedhorn 6.18 (1) + (2)      | ~200           | (project-local)        |
| Layer 5: audit-pass-2 trio           | ~300           | (project-local)        |
| Layer 6: AuditCleanWrappers file     | ~150           | (project-local)        |
| **Total**                            | **~1070**      |                        |

Plus mathlib gap #36 (Stacks 00MA: `AdicCompletion` of noetherian is
noetherian) — ~150 lines, also upstreamable.

## Verification pass

Cross-checking the proof outline against three sources:

| Statement | Wedhorn | Huber [Hu3] | BGR |
|-----------|---------|-------------|-----|
| Banach OMT for Tate-ring modules | 6.16 ("Missing") | Lemma 2.4(i) | Prerequisite §3.7 |
| Noetherian ⇔ ideals closed | 6.17 ("Missing") | (implicit via 2.4) | 3.7.2/2 ✓ |
| Unique complete fg-module topology | 6.18(1) ("Missing") | Lemma 2.4(ii) | 3.7.3/3 ✓ |
| A-linear maps continuous + strict | 6.18(2) ("Missing") | Lemma 2.4(ii) | 3.7.3/2 + Cor 5 ✓ |
| **Underlying analytical input** | Bourbaki [B1] 1.3.3 | [B1, 1.3.3] | "Open Mapping Theorem for Banach spaces" (prerequisite) |

All three sources agree: the only substantive input is **Banach's OMT for
complete metric topological groups**. The rest is classical commutative
algebra (Nakayama, Hilbert basis, Krull intersection) + Baire's theorem
(both in mathlib).

## Next step: invoke `/develop` for the binding decomposition

The user observed correctly that this kind of ticket-board generation is
now `/develop`'s job — the skill description says it runs a "binding
**methodical decomposition pre-work pass** — for each top-level result,
writes the prose proof, decomposes into ordered lemmas, **writes every
lemma as a `:= by sorry` declaration in the project's Lean files (the
skeleton must `lake build` clean)**, tensions against the references with
**verbatim source quotes per leaf plus a Lean ↔ source match paragraph**,
and verifies that every leaf is dischargeable from existing mathlib or
already-developed project code". This is exactly the methodology we need
for the Layer 1-6 ticket board above.

Invoke as `/develop <topic>` with the top-level result being
`isStronglyNoetherian_of_isNoetherianRing_isTateRing` (or equivalently
the whole 6.18 chain). `/develop` will:

1. Write the prose proof per layer using the BGR / Huber sources above.
2. Decompose into ordered lemmas matching Layers 1-6.
3. Write each lemma as `:= by sorry` skeleton, ensuring `lake build` stays clean.
4. Attach verbatim BGR / Huber / Wedhorn quotes to each leaf.
5. Verify each leaf has a mathlib lemma or project-existing infrastructure
   discharge (or surface the API gap explicitly).
6. Save `decomposition.md` + write the ticket board.
