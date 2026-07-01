# Plan — LMFDB labels for classical modular forms

**Goal.** A Lean function assigning the LMFDB newform label `N.k.a.x` to a classical newform
(Galois orbit) of level `N`, weight `k`, provably canonical (Galois-invariant + injective on
orbits) and matching LMFDB's ordering conventions. Optional extension: complex-embedding labels
`N.k.a.x.n.i`.

**Label format** (confirmed, lmfdb.org/knowledge/show/cmf.label):
`N` level · `k` weight · `a` Dirichlet-character **Galois-orbit** label · `x` newform
**Galois(Hecke)-orbit** label. Embedding form `N.k.a.x.n.i`: `n` = Conrey index of the character,
`i` = embedding index ordered by the eigenvalue vector (ℂ ordered real-part then imaginary-part).
Letters are bijective base-26: `a,b,…,z,ba,bb,…`.

## Dependency note — the open `mainLemma` is NOT on the critical path
Labels need *multiplicity one* (distinct newform orbits ⇔ distinct Hecke eigensystems, so the
trace-ordering is well-defined). That is `strongMultiplicityOne_axiom_clean` — **already proven
axiom-clean**, with no dependency on the open general `mainLemma` (it uses the proven
per-character `mainLemma_charSpace_routeB`). So labeling builds on proven foundations.

## What exists vs. what's missing
HAVE (LeanModularForms): `Newform`, `cuspFormsNew`, SMO, q-expansions/`fourierCoeff`, Hecke
eigenvalues, Nebentypus characters `(ZMod N)ˣ →* ℂˣ` / mathlib `DirichletCharacter`.
HAVE (mathlib): `DirichletCharacter` (conductor/primitive/GaussSum/orthogonality), full
`NumberField`/`IsGalois`/`Gal`/integral-closure/algebraic-closure API, `List.mergeSort`.
MISSING (must build — none in mathlib): Dirichlet-character **Galois orbits** + Conrey indexing +
LMFDB orbit ordering; newform **coefficient field** + **Galois action on newforms** + orbits +
trace-sequence ordering; the base-26 letter encoding; the label assembly + canonicity.

## Phased decomposition (tickets)

**Phase 0 — label encoding (trivial, no deps).**
- `Nat ≃ String` bijective base-26 (`a,b,…,z,ba,…`) + inverse; prove bijective/monotone.
  (Candidate home: `Common/`.) Small.

**Phase 1 — character-orbit label `a` (tractable, self-contained, NO newforms — the first foothold).**
- 1a. Conrey indexing: the iso `(ZMod N)ˣ →* ℂˣ` ↔ Conrey index `m ∈ (ZMod N)ˣ` (mathlib may lack
  it — likely build). Order of a character.
- 1b. Galois action on characters: `χ ↦ χ^t`, `t` coprime to `ord χ`; the **Galois orbit** =
  `{χ^t}`. (Equivalently the `(ZMod (ord χ))ˣ`-orbit.) Finiteness, orbit invariants.
- 1c. LMFDB orbit ordering — **CONFIRMED** (arXiv:2002.04717 §Labels + knowl
  `character.dirichlet.galois_orbit_label`): orbits of modulus `N` are ordered **lexicographically
  by `(ord χ, Tr χ(1), Tr χ(2), Tr χ(3), …)`**, the absolute-trace tuple `Tr_{ℚ(χ)/ℚ}`. (NOT
  "sorted Conrey indices" — that's only LMFDB's canonical orbit *representative*, not the ordering
  key.) Encoded structurally as `orbitTraceAt χ j := Σ_{ψ∈orbit} ψ(j)` (= `Tr χ(j)`, orbit-invariant);
  letter = base-26 of `index-1` via Phase 0.

**STATUS (2026-06-17): Phase 0 + Phase 1 COMPLETE — sorry-free, build green.** Files
`Labels/Encoding.lean` + `Labels/CharacterOrbit.lean` (wired into `LeanModularForms.lean`).
The character-orbit label `a` is **canonical**: `charOrbitLabel` is proven both **constant on Galois
orbits** (`charOrbitLabel_eq_of_isGaloisConj`) and **injective on orbits** (`charOrbitLabel_injOn_orbits`)
— `orbitIndex_inj` via a generic `rank_injOn` (rank map strictly monotone), and `orbitRankKey_injOn_orbits`
via mathlib `linearIndependent_monoidHom` (Artin–Dedekind: the trace tuple `Σ_{ψ∈orbit} ψ(j)` separates
distinct orbits). Zero sorries in `Labels/{Encoding,CharacterOrbit}`.

**Phase 2 (`Labels/NewformOrbit.lean`) — framework DONE, build green.** Mirrors Phase 1: Galois-conjugacy
`Setoid` → `galoisOrbit` → orbit-invariant `traceSeqAt` (= `Tr_{K_f/ℚ}(aₙ)`) → `orbitIndex` → `newformOrbitLabel`,
with `newformOrbitLabel_eq_of_isGaloisConj` proven (orbit-invariant) and `newformOrbitLabel_injOn_orbits`
reduced to `traceSeq_injOn_orbits`. The SMO-separation `coeffSeq_injOn_charSpace` is **sorry-free from
`strongMultiplicityOne_axiom_clean`**. **Now only 2 isolated deep-NT sorries** (2026-06-17, NewformOrbit 4→2):
`coeffSeq_isIntegral` (Hecke eigenvalues are algebraic integers — Shimura 3.52/Deligne) and
`instFiniteDimensionalCoeffField` (`[K_f:ℚ]<∞`) — both **isolated + unconsumed** (only their own docstrings
reference them; NOT on the label map's critical path). The former finiteness/injectivity sorries
`instFiniteNewform` + `traceSeq_injOn_orbits` are now **closed axiom-clean** (see resolved FINDING below).
**Phase 3 (`Labels/Label.lean`) — DONE, sorry-free.** `Newform.lmfdbLabel f = "N.k.{charOrbitLabel χ_f}.{newformOrbitLabel f}"`
(χ_f = `Eigenform.χ` via `Newform.dirichletLift`), with `lmfdbLabel_eq_of_isGaloisConj` (Galois-invariant, axiom-clean,
composing Phase 1 + Phase 2) and `lmfdbLabel_injOn_orbits` (via label-parsing back to components). Full canonical label map in place.

**✅ RESOLVED (2026-06-17) — finiteness + injectivity closed.** The earlier blocker (`Eigenform.ringEigenvalue`
free at bad primes ⇒ `Newform` not determined by its form ⇒ `instFiniteNewform`/`traceSeq_injOn_orbits` false) is
**fixed**. Added field `Eigenform.ringEigen_bad : ∀ n, ¬Coprime n.val N → ringEigenvalue n = 0` (commit `f704590`;
the one construction site `eigenformOfIsEigenform` in `StrongMultiplicityOneFull.lean` updated to guard `.choose`
with `if Coprime … else 0`). A newform is now **determined by its underlying form**
(`Newform.{toCuspForm,coeffSeq}_injective`: χ pinned via `cuspFormCharSpace` + diamond action on the nonzero form;
`ringEigenvalue` pinned by the unique good-prime eigenvalue + `ringEigen_bad`). Then (commit `2936f0a`):
`instFiniteNewform` via `linearIndependent_toCuspForm.finite` (distinct newforms are Petersson-orthogonal ⇒ LI,
in the finite-dim cusp space `cuspForm_finiteDimensional`); `traceSeq_injOn_orbits` via `linearIndependent_coeffSeq`
(the newform analogue of `linearIndependent_monoidHom`). **The full LMFDB label map + canonicity
(`lmfdbLabel_eq_of_isGaloisConj`, `lmfdbLabel_injOn_orbits`, `newformOrbitLabel_injOn_orbits`, `instFiniteNewform`)
is now axiom-clean `[propext, Classical.choice, Quot.sound]`**; SMO headline stays axiom-clean. The 2 deep sorries
above remain (unconsumed, off the critical path).
- Deliverable: `charOrbitLabel : DirichletCharacter ℂ N → String`; well-defined (constant on
  orbits) + injective on orbits.

**Phase 2 — newform-orbit label `x` (the bulk, greenfield).**
- 2a. Coefficient (Hecke) field of a newform: the number field `K_f := ℚ(aₙ(f))`; the `aₙ` are
  algebraic integers; `[K_f:ℚ] < ∞`. Build on mathlib `NumberField`/integral-closure.
- 2b. Galois action on newforms: `σ ∈ Gal(ℚ̄/ℚ)` sends `f ↦ σf` (conjugate `aₙ`), again a newform
  of the same `N,k` (character conjugated); the **Galois/Hecke orbit** of `f`; finiteness
  (= `[K_f:ℚ]`).
- 2c. Orbit trace invariant: `Tr_{K_f/ℚ}(aₙ)` (∈ ℤ), the orbit-level sequence used for ordering.
- 2d. LMFDB ordering within `(N,k,a)`: lexicographic on the Fourier/trace sequence (LMFDB orders
  newforms lexicographically by Fourier coefficients) → letter via Phase 0. Distinct orbits ⇒
  distinct sequences by **SMO**. ⚠️ CONFIRM exact key (dim then trace-of-aₚ then aₙ?) vs lmfdb source.
- Deliverable: `newformOrbitLabel : Newform N k → String`; constant on Galois orbits + injective
  on orbits (via SMO).

**Phase 3 — assembly + canonicity.**
- `lmfdbLabel (f : Newform N k) : String := s!"{N}.{k}.{charOrbitLabel χ_f}.{newformOrbitLabel f}"`.
- Canonicity theorem: Galois-invariant + the induced map {newform Galois orbits} → labels is
  injective (well-defined bijection onto its image), via Phases 1c/2d + SMO.
- (Optional, later) embedding labels `.n.i` (Conrey index + eigenvalue-vector ordering).

## Risks / decisions
- **Exact LMFDB ordering keys** (1c tiebreak, 2d trace-order details) — must match lmfdb source
  verbatim to legitimately be "LMFDB labels"; confirm against github.com/LMFDB/lmfdb before fixing
  the definitions.
- **Structural vs executable — DECIDED (owner, 2026-06-16): canonical labeling function +
  well-definedness** (provable target). NOT the executable computation layer (decidable equality on
  coefficient fields, computing a concrete form's `23.1.b.a`) — that's explicitly out of scope.
- **Conrey correspondence** likely needs building (mathlib gap); reusable → `Common/`.
- Phase 2 is the heavy, mostly-greenfield half (Galois-on-newforms + coefficient fields); Phase 1
  is self-contained and the right place to start.

## Suggested order
Phase 0 → **Phase 1 (start here)** → Phase 2 → Phase 3. Phase 1 exercises the orbit+ordering+letter
machinery that Phase 2 reuses, and delivers a complete component (`a`) on its own.
