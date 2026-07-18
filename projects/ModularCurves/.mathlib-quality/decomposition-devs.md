# Decomposition: DEV-1 (flat-locus local openness) + DEV-2 (07RF colimit) — the D-chain's last two boxes

Both TOR-FREE, both mathlib-absent at the top but with MORE foundation present than earlier
delegates assumed. Source: Stacks 00RC/00LP/00N1/00RB/00MI (DEV-1), 07RF/10.128.3 (DEV-2).

## mathlib survey (decisive — grounds the route decisions)
- **Projective-dimension theory PRESENT** (DEV-1 foundation, richer than expected):
  `RingTheory/Regular/ProjectiveDimension.lean` — `projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular`
  (regular element raises proj dim by 1 — THE inductive step of Hilbert syzygy),
  `projectiveDimension_quotient_eq_length` (regular sequences), `hasProjectiveDimensionLT_of_forall_finite`;
  `RingTheory/LocalProperties/ProjectiveDimension.lean` — `hasProjectiveDimensionLE_iff_forall_primeSpectrum/_maximal`
  (LOCAL characterization), `projectiveDimension_le_of_isLocalizedModule`. `CategoryTheory/Abelian/Projective/Dimension.lean`
  (`projectiveDimension`, `ProjectiveResolution`).
- **ABSENT** (must build, DEV-1): Hilbert syzygy (`gldim κ[x₁..xₙ] = n` — but BUILDABLE from the
  regular-element step by induction), Buchsbaum-Eisenbud exactness (00N1), finite-free-resolution-of-fp
  as a concrete `CochainComplex` (only categorical `ProjectiveResolution` exists).
- **AffineTransitionLimit PARTIAL** (DEV-2 foundation): `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`
  (fp morphism factors through a stage), the directed-limit-of-affine-schemes + quasi-compactness machinery.
  ABSENT: explicit "flatness descends along a limit of rings (module form)" — must build on the limit machinery.
- **PROVEN (ours)**: T-LC1 `Module.free_of_flat_of_fibre_free` (00MH, axiom-clean); `isOpen_flatLocus`
  (modulo DEV-1's box); `flat_of_flatLocus_univ`; `Module.Flat.lTensor_exact`; Nakayama; NOETH1/2.

## DEV-1 route decision: proj-dim foundation, NOT Buchsbaum-Eisenbud from scratch
The Stacks 00RC route uses Buchsbaum-Eisenbud (00N1). But mathlib's proj-dim machinery gives a
LEANER route to the SAME local-openness content: over the fibre poly ring κ(𝔭)[x] (finite global
dim by Hilbert syzygy, buildable), a finite-type module has FINITE projective dimension ⟹ its
high syzygy is projective(=free locally) ⟹ T-LC1 (00MH) upgrades fibre-freeness+R-flatness to
S-freeness ⟹ M free near 𝔮 ⟹ flat near 𝔮. **Buchsbaum-Eisenbud may be AVOIDABLE** — its role
(fibre-exactness detection) is subsumed by "finite proj dim ⟹ syzygy projective" + T-LC1. MAKE-OR-BREAK:
whether the proj-dim route closes the local-openness without the full 00N1 exactness criterion (T-DEV1c).

### [T-DEV1a] Hilbert syzygy: gldim of a polynomial ring over a field
- `hasProjectiveDimensionLE (MvPolynomial (Fin n) K) (fin-module) n`-shape (K a field), by induction on n
  via `projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular` (the xᵢ are a regular sequence) +
  `hasProjectiveDimensionLE_iff_forall_...`. Buildable from present machinery. ~100-150 lines.
### [T-DEV1b] finite free resolution of an fp module over a Noetherian ring (00LP)
- M fp over noeth S ⟹ ∃ a resolution by finite free S-modules (iterate `S^n ↠ M`, kernel fg by noeth).
  As a concrete `CochainComplex` or an inductive syzygy chain. ~100 lines.
### [T-DEV1c] local openness at a flat point (fill `exists_basicOpen_subset_flatLocus_of_mem`) — THE ASSEMBLY
- Using T-DEV1a (finite gldim of the fibre), T-DEV1b (resolution), T-LC1 (00MH), + `Module.Flat.lTensor_exact`:
  at a flat 𝔮, the syzygy at the fibre's gldim is R-flat with free fibre ⟹ free near 𝔮 (T-LC1) ⟹ the
  resolution truncates + spreads to a nbhd ⟹ M flat there. ~200-300 lines. MAKE-OR-BREAK (does the proj-dim
  route avoid 00N1?). If not, add [T-DEV1b'] Buchsbaum-Eisenbud 00N1 as a further sub-ticket.

## DEV-2 route decision: build on AffineTransitionLimit
### [T-DEV2a] flatness descends along a directed colimit of rings (07RF module form)
- `M = colimᵢ Mᵢ` over `R = colimᵢ Rᵢ` (fp data), M flat over R ⟹ Mᵢ flat over Rᵢ for large i. Via
  `flat_of_flatLocus_univ` (flatness = flat locus univ) + `isOpen_flatLocus` (flat locus of Mᵢ over Rᵢ is
  open) + the AffineTransitionLimit quasi-compactness/limit machinery (the open flat locus at the colimit
  = univ ⟹ some finite stage has flat locus ⊇ any given quasi-compact ⟹ = univ after enlarging). ~200-300
  lines. Depends on isOpen_flatLocus (⟸ DEV-1).
### [T-DEV2b] fill `exists_flatLocus_univ_stage`
- Thin wrapper of T-DEV2a onto the NoethApprox colimit (R = colim fg-ℤ-subalgebras). ~50-100 lines.

## Feasibility verdict
BOTH Tor-free and buildable; mathlib's proj-dim + AffineTransitionLimit foundations are richer than
the earlier delegates exploited. DEV-1 ~400-550 lines (make-or-break: does proj-dim avoid Buchsbaum-Eisenbud
in T-DEV1c; if not, +00N1 ~200 lines). DEV-2 ~250-400 lines. Total ~650-950 lines across ~5 tickets, several
genuinely hard (Hilbert syzygy, the 00RC assembly, the colimit flatness-descent). Order: DEV1a→DEV1b→DEV1c
(unblocks isOpen_flatLocus axiom-clean) ‖ DEV2a→DEV2b (unblocks NOETH3), then FLAT1 axiom-clean ⟹ D-chain done.
Make-or-break to attempt FIRST: T-DEV1a (Hilbert syzygy — validates the proj-dim route) then T-DEV1c.
