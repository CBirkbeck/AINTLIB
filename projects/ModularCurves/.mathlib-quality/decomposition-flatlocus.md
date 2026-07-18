# Decomposition: flat-locus openness → box discharge (TOR-FREE route)

**Goal:** discharge the D-chain's last `sorryAx` (T-FLAT1-SLICE box). Chain:
`box ← 07RF (colimit flatness-descent) ← 00RC (flat-locus openness) ← 00MH/00MI (fibre
criteria)`. 

## THE ROUTE DECISION (make-or-break, resolved TOR-FREE)

The GF6 delegate hit the "local criterion of flatness" wall and assumed it needs
derived-functor Tor (a multi-week foundational build → the B3 report). **That was wrong.**
Source study + mathlib survey show the specific consequences 00RC needs — the fibre
criteria **00MH** ("freeness from fibre freeness") and **00MI** — are provable **WITHOUT
building Tor**, because the only "Tor₁-vanishing" they use is *flatness of the module
itself*, which is the HYPOTHESIS, delivered by mathlib's `Module.Flat.lTensor_exact`.

### mathlib survey (grounds the Tor-free route — all CONFIRMED present)
- `Module.Flat.lTensor_exact` [Flat R M] (Flat/Basic.lean:323): flat ⟹ a short exact
  sequence stays exact after `M ⊗ -`. THIS is the Tor₁^R vanishing, for free from the
  flatness hypothesis. Also `rTensor_preserves_injective_linearMap`, `rTensor_injective_of_fg`.
- Nakayama: full suite `RingTheory/Nakayama.lean` (`eq_bot_of_le_smul_of_le_jacobson_bot`,
  `eq_smul_of_le_smul_of_le_jacobson`, ...).
- `Module.free_of_isLocalizedModule` (LocalProperties/Projective.lean:37); free-from-local API.
- **Openness criterion PRESENT**: `PrimeSpectrum.isOpen_of_stableUnderGeneralization_of_isConstructible`
  (RingTheory/Spectrum/Prime/ConstructibleSet.lean:168, `@[stacks 00I0]`): on `Spec R`,
  `StableUnderGeneralization ∧ IsConstructible ⟹ IsOpen`. `isConstructible_basicOpen`
  (Spectrum/Prime/Topology.lean:1153). Full `IsConstructible` boolean API
  (Topology/Constructible.lean).
- **ALREADY PROVEN (ours, FlatLocus.lean)**: `flatLocus_stableUnderGeneralization`,
  `flat_localizedModule_of_flat` (engine), `basicOpen_subset_flatLocus_of_free`
  (generic-flatness neighbourhood).

TWO viable Tor-free assemblies of 00RC once 00MH/00MI are in hand — pick the cleaner at
execution: (i) Stacks 00RC's own resolution route (00MH/00MI directly, now Tor-free); or
(ii) route (B): flat locus is constructible (via 00MH + generic flatness GF5 neighbourhood +
Noetherian induction) then apply the mathlib openness criterion + our generization-stability.

## Ticket tree

### [T-LC1] freeness from fibre freeness (Stacks 00MH = Lemma 10.129.1 / Matsumura 22.5)
- Statement: `R→S`, M a finite S-module, 𝔮∈Spec S over 𝔭∈Spec R, M flat over R at 𝔮,
  `M ⊗_R κ(𝔭)` free over κ(𝔭) ⟹ `M_𝔮` free over `S_𝔮`.
- Proof (Tor-free): Nakayama-lift a κ(𝔭)-basis of `M⊗κ(𝔭)` to `φ : S_𝔮^r → M_𝔮` (iso mod 𝔮).
  `K = ker φ`. M flat over R ⟹ `0→K→S^r→M→0` stays exact after `⊗_R κ(𝔭)`
  (`Module.Flat.lTensor_exact`) ⟹ `K⊗κ(𝔭)` injects into `κ(𝔭)^r` and its image is 0
  (φ⊗κ iso) ⟹ `K⊗κ(𝔭)=0` ⟹ `K = 𝔭K ⊆ 𝔪_𝔮 K`; K fg (S noeth) ⟹ Nakayama ⟹ K=0 ⟹ M_𝔮 free.
  **THE MAKE-OR-BREAK — attempt FIRST; all pieces confirmed present.** ~100-150 lines.

### [T-LC2] flatness/exactness from fibres (Stacks 00MI/00RB)
- The companion criterion assembling 00MH across a finite free resolution: a bounded complex
  of finite frees that is exact on the fibre κ(𝔭) and flat over R is exact near 𝔮 with flat
  cokernel. Same Tor-free toolkit (00MH + Nakayama + flat-tensor-exactness). ~100-150 lines.

### [T-LC3] openness of the flat locus (Stacks 00RC / Thm 10.129.4) — discharge isOpen_flatLocus
- Statement: `isOpen_flatLocus` (already stated + boxed in FlatLocus.lean). Assemble from
  T-LC1/T-LC2 via EITHER (i) the resolution route, OR (ii) `IsConstructible` (from T-LC1 +
  GF5 neighbourhood + Noetherian induction) + `isOpen_of_stableUnderGeneralization_of_isConstructible`
  + the proven generization-stability. ~150-250 lines. Removes FlatLocus's box.

### [T-GF7] flatness descends in a directed colimit (Stacks 07RF = 10.168.1(3))
- Discharge `exists_noetherian_descent_flat`'s `Module.Flat R₀ A₀` box (NoethApprox.lean),
  via T-LC3 (00RC) + the colimit bookkeeping (source fetched, in-hand). ~100-200 lines.

### [T-NOETH-FLAT1] discharge the T-FLAT1-SLICE box
- `nonZeroDivisor_of_flat_of_fibrewise_nonZeroDivisor` via NOETH1/2 (done) + T-GF7 (NOETH3)
  + Nakayama at the noeth stage. ~150 lines. ⟹ **entire D-chain axiom-clean.**

## Feasibility verdict
**Tor-free and BOUNDED** — NOT the foundational Tor build the B3 report feared. Total
~600-900 lines across 5 lemmas, all using mathlib-present machinery (flat-tensor-exactness,
Nakayama, the constructible/openness criterion). The make-or-break is T-LC1 (00MH); if its
Tor-free proof lands (pieces confirmed present), the whole chain opens. Generic flatness
(GF5, being finished) feeds route (ii) but the resolution route (i) doesn't even need it.
