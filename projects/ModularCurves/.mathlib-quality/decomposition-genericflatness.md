# Decomposition: Generic Flatness → box discharge (T-NOETH-FLAT1 chain)

**Goal:** discharge the D-chain's last `sorryAx` — the T-FLAT1-SLICE box
(`nonZeroDivisor_of_flat_of_fibrewise_nonZeroDivisor`, LevelStructure/CartierDivisor.lean).
Chain: box ← NOETH-FLAT1 discharge ← NOETH3 flatness-descent ← flat-locus openness ←
**generic flatness (Stacks 051R)** ← {prime-quotient filtration, extension-of-free,
Noether-normalization-over-domain, support-annihilation}.

**Source (fetched, verbatim-transcribed 2026-07-07):** Stacks Tag 051R = Lemma 10.118.1,
"Generic Flatness (Noetherian case)": *R Noetherian domain, R→S finite type, M finite-type
S-module ⟹ ∃ 0≠f∈R with M_f free over R_f.* PROOF = dévissage inducting on d = dim(S_K),
K = Frac(R):
1. Filtration of M with quotients S/𝔮 (Stacks 10.62.1); extensions of free are free
   (Stacks 0516) ⟹ reduce to M = S a domain.
2. Kernel case: ker(R→S) ≠ 0 ⟹ take f in it, S_f = 0, trivial (d = −1 base).
3. Domain case: Noether-normalise R ⊂ R[y₁..y_d] ⊂ S (2nd finite; Stacks 10.115.7 over
   K); basis z₁..z_r of Frac(S)/Frac(R[y]); SES 0→R[y]^r→S→N→0 with N finite,
   support avoids the generic point of Spec R[y]; nonzero g∈R[y] kills N (Stacks 10.40.5);
   N over S'=R[y]/(g) has dim(S'_K)<d ⟹ induction gives f with N_f free; R[y]_f free ⟹
   S_f free.

## Leaf feasibility (mathlib survey 2026-07-07, verified by grep/#check)

- **[T-GF1] prime-quotient filtration** (Stacks 10.62.1): a finite module over a
  noetherian ring has a filtration `0=M₀⊂…⊂Mₙ=M` with `Mᵢ/Mᵢ₋₁ ≅ R⧸𝔭ᵢ`, 𝔭ᵢ prime.
  **mathlib: ABSENT.** Building blocks present: `associatedPrimes.nonempty
  [IsNoetherianRing R][Nontrivial M]` (AssociatedPrime/Basic.lean), noetherian induction.
  Own sub-development ~100-200 lines (pick an associated prime 𝔭 = ann(x), R⧸𝔭 ↪ M via
  x, recurse on M/(R·x) by noetherian induction). Statement is a `RelSeries`/inductive.
- **[T-GF2] extension of free is free** (Stacks 0516): SES `0→A→B→C→0` of R-modules, A
  and C free ⟹ B free. **mathlib: ABSENT as such** (has `Free.of_basis` etc. but not the
  SES form). Small ~30 lines: C free ⟹ projective ⟹ SES splits ⟹ B ≅ A⊕C ⟹ free. (NOTE:
  051R only needs C free where C = successive quotient S/𝔮 — but in the induction it's
  applied with C = R_f-free pieces; the split form suffices.)
- **[T-GF3] Noether normalization over a domain** (Stacks 10.115.7): R domain, S domain
  finite-type ⟹ ∃ y₁..y_d ∈ S with R[y]→S finite after inverting some 0≠f∈R (spread the
  field-base normalization of S_K over K down to R_f). **mathlib: field-base present**
  (`RingTheory/NoetherNormalization.lean`, Nagata, over a field `k`); needs the
  fraction-field application + spreading-out wiring ~100 lines.
- **[T-GF4] support-avoidance annihilation** (Stacks 10.40.5): N finite, 𝔭 ∉ support N ⟹
  ∃ g ∉ 𝔭 with g·N = 0. **mathlib: MOSTLY PRESENT** —
  `Module.mem_support_iff_exists_annihilator` (RingTheory/Support.lean) + N finite ⟹
  ann(N) determines support; ~20 lines of wiring.
- **[T-GF5] generic-flatness dévissage** (Stacks 051R main): the induction assembling
  GF1-4. **The glue ~150 lines** (strong induction on d, the SES construction, the
  R[y]_f-freeness transport).

## Further layers (each its own sub-development, on top of generic flatness)

- **[T-GF6] flat-locus openness** (Stacks 00R4/052F): for M fp over noetherian R, `{𝔭 :
  M_𝔭 flat}` is open in Spec R. PROOF = Noetherian induction using generic flatness
  (generic flatness ⟹ flat on a dense open; recurse on the closed complement). **ABSENT.**
  ~150-250 lines on top of GF5.
- **[T-GF7 = NOETH3 discharge] colimit flatness descent** (EGA IV 11.2.6): the
  `Module.Flat R₀ A₀` component of `exists_noetherian_descent_flat` — A=colim flat ⟹ A₀
  flat at some stage, via flat-locus openness of A₀ over the noetherian R₀. ~100-200 lines
  wiring GF6 to the NoethApprox colimit.
- **[T-NOETH-FLAT1] box discharge**: `nonZeroDivisor_of_flat_of_fibrewise_nonZeroDivisor`
  via NOETH1+2+3 (descend to noeth stage) + Nakayama (Ann(f) fg there). ~150 lines.

## Honest scale (the /develop feasibility verdict)

FAITHFUL to the source — no invented route; Stacks 051R IS this dévissage, there is no
shorter path (verified: mathlib has no generic flatness/freeness, no flat-locus openness).
But the total is **genuine mathlib-PR-scale**: generic flatness alone (GF1-5) is
~400-600 lines building the prime-quotient filtration FROM SCRATCH (itself absent) +
Noether-normalization-over-domain wiring + dévissage; then GF6 (flat-locus openness) +
GF7 (colimit descent) + FLAT1 (box) add ~400-550 more. **~800-1150 lines across ≥8
substantial lemmas, spanning 4 conceptual layers.** This is a multi-week formalization —
the size of a real mathlib contribution (generic flatness is a known "big" target).

RED-FLAG-4 note (binding /develop discipline): this pass HIT "substantial infrastructure
absent from mathlib." I RE-READ the source (Stacks 051R, fetched) and confirmed the route
is faithful — the infrastructure is the GENUINE content, not a decomposition artifact.
So it is a legitimate (large) target, not a planning error. The decision is scale/appetite,
which is the owner's call (surfaced for approval per /develop 1i).
