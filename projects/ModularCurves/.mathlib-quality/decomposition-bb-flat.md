# Decomposition — [BB-FLAT] `mulByHom_flat`: `[N] : E → E` is flat (KM 2.3.1) — D2's box

**Scoped by beastmode-D2, 2026-07-09 (fleet-saturation hold, zero-build planning).** BB-FLAT is D2's
box per board v10.29 (`P3b3 MASTER + D2 BB-FLAT own it`) / lines 8724, 8866. TARGET (in stream-B's HELD
`EllipticCurve/Torsion.lean:147` — **bridge, do NOT edit the held file**; the proof lands in a D2 file,
the holder wires it with one `exact`):
```lean
theorem mulByHom_flat (N : ℕ) [NeZero N] : Flat (E.mulByHom N)   -- E : EllipticCurve S, S ARBITRARY
```
`Flat` = the scheme morphism `[N] : E.E ⟶ E.E` is flat. Consumer chain (board 8724):
`torsionFixed_of_fixesLevel ⟸ E[N]-finite-étale ⟸ {P3b3's MASTER, D2's BB-FLAT}`; `E[N] = pullback (mulByHom N) zero`,
so BB-FLAT ⟹ `torsionπ` flat (finite locally free of rank N²). Modular-curves path routed AROUND this (v10.37) —
so it is a quality/completeness box, not a curve blocker; discharge on D2's schedule.

## 0. THE KEY CONSTRAINT: `S` is an ARBITRARY base
`E : EllipticCurve S` for a general scheme `S` (NOT assumed regular/noetherian). This decides the routes:
a "miracle flatness" argument (finite morphism between REGULAR schemes of equal dimension ⟹ flat) cannot
apply directly over `S`; it must run over the UNIVERSAL (regular) Weierstrass base and descend. The
fibrewise-flatness route runs over general `S` directly. Two routes, evaluated below.

## 1. KM 2.3.1 source route (locator: KM §2.3, print ~p.45; read verbatim when grinding)
Torsion.lean docstring (project transcription): "[N] finite locally free of degree N², via Hasse's
`deg[N]=N²` on fibres + fibrewise flatness criterion." BB-FLAT docstring names both classical routes:
(A) "miracle flatness over the universal (regular) Weierstrass base [AK-1, V, 3.6]"; (B) "general fibrewise
criterion EGA IV 11.3.10". **ACTION when grinding: read KM §2.3 (2.3.1) verbatim to confirm which KM
actually uses + the exact hypotheses** (this scoping is from the docstrings + references, not yet the KM text).

## 2. ROUTE A — fibrewise flatness criterion (EGA IV 11.3.10) = D2's flat-locus toolbox ★ RECOMMENDED
This is the general-base route, and it is EXACTLY what the whole B–E / flat-locus D-chain was built for.
EGA IV 11.3.10: a finitely-presented morphism is flat iff it is flat on all fibres AND the flat locus is
open-and-everything — i.e. our **`FlatLocus.flatLocus_spreads_of_flat` (00RC/00RB openness) + 00MI
(fibre-exact ⟹ flat)**. Leaf structure:
- **[BBF-A1] fibrewise input**: `[N]` is flat on every geometric fibre `E_s̄` — over a field, `[N] : E_s̄ → E_s̄`
  is a nonconstant morphism of smooth proper curves, hence finite flat (a finite morphism of Dedekind/1-dim
  regular schemes is flat — the miracle-flatness FIBRE case, which IS available: over a field the base is a
  point, `E_s̄` is a smooth curve = 1-dim regular, `[N]` finite ⟹ flat). The `E[N](k̄) ≅ (ℤ/N)²` structure is
  **already proved over fields** in `HasseWeil/.../NTorsion/TorsionGeneralN.lean` (Silverman III.6.4). Locator:
  KM 2.3.1 "Hasse `deg[N]=N²` on fibres". ~bridged from HasseWeil via T-B6 (P3b3's fibre-comparison) — SHARED edge.
- **[BBF-A2] flat-locus openness over the (fp) base**: `flatLocus R S M` open + spreads (00RB) — the
  D-chain result. **STATUS CORRECTED 2026-07-09**: NOT "99.5% done". The B-E *component* lemmas
  (FittingIdeals/McCoy, Grade/Rees, Depth API, 00N0 Peskine–Szpiro) ARE axiom-clean; but the *assembly*
  above them is skeletal — the B-E criterion is gated on **[T-BE-TAIL]** (2 mutually-recursive tail
  sub-cases: 00MW split-top peeling + interior-gap truncation, both dependent-type complex surgery,
  `BuchsbaumEisenbud.lean:846,858`), and the whole flat-locus layer (00ME `:118`, 00MI `:1156`, 00RB
  `:1138`, T-REDUCEP `:1176`, T-FINAL `:1200`) is still `sorry`. This is the load-bearing dependency.
- **[BBF-A3] assembly (00MI)**: fibre-flat + flat-locus-open ⟹ flat everywhere. `coker_flat_of_specialFibreExact`
  is **STILL A SORRY** (`BuchsbaumEisenbud.lean:1156` — my earlier "axiom-clean, done" was WRONG). Its
  hypothesis predicate `SpecialFibreExact` is now authored (2026-07-09), but the 00MI proof itself
  (induction from 00ME) is unproven. `flat_of_flatLocus_univ` (NoethApprox) + base-change are the easy tail.
- **GATE**: [BBF-A2] = [T-BE-TAIL] (the flat-locus openness bottoms out at B–E, D2's 99.5% residual). When
  T-BE-TAIL lands ⟹ FlatLocus axiom-clean ⟹ BB-FLAT-Route-A discharges. **This closes the loop: BB-FLAT is
  the intended downstream consumer of the entire B–E development.** LOC after T-BE-TAIL: ~150–300 (assembly +
  the fibrewise bridge + base-change), all on PROVEN toolbox (00MH/00MI/00RB/NOETH).

## 3. ROUTE B — miracle flatness over the universal regular Weierstrass base — NOT recommended (mathlib-absent)
"Finite morphism between regular schemes of the same dimension is flat" [AK-1 V.3.6 = miracle flatness].
Run over the UNIVERSAL Weierstrass base `Spec ℤ[a₁,…,a₆][Δ⁻¹]` (regular), then descend to `S` by base change
(flatness stable under base change). Leaves:
- **[BBF-B1] miracle-flatness theorem**: finite between regular local rings of equal dim ⟹ flat. **mathlib
  ABSENT** (zero-build survey 2026-07-09: no `IsCohenMacaulay`, no `flat_of_finite_of_regular`). Would need
  Cohen–Macaulay theory (depth = dim) + Auslander–Buchsbaum-adjacent — a substantial NEW development (and
  our Depth API `HasDepthGE` is a partial foundation, but CM/miracle-flatness is not built). ~large.
- **[BBF-B2] universal Weierstrass base is regular** + `E` over it is regular (smooth over regular) — needs
  the universal-Weierstrass-scheme setup (project has EllipticCurve over a base; the universal base regularity
  is a further fact). **[BBF-B3] descent**: `[N]` flat over universal base + base-change `S → universal` ⟹
  `[N]_S` flat (flat stable under base change, mathlib HAVE) — the one easy leaf.
- **Verdict**: Route B's crux [BBF-B1] (miracle flatness / CM) is mathlib-absent and independent of the B–E
  work — a SEPARATE large gate. Not the path while Route A's dependency (T-BE-TAIL) is D2's own near-done residual.

## 4. RECOMMENDATION + STATUS
**Route A (flat-locus / fibrewise, D2's toolbox) is still the path**, but the gate is BIGGER than a single
residual (corrected 2026-07-09 after auditing the actual `sorry` inventory). BB-FLAT is the intended downstream
consumer of the B–E / flat-locus D-chain, but discharging it needs the WHOLE flat-locus assembly layer, not just
[T-BE-TAIL]: closing [T-BE-TAIL] makes only the **B-E criterion** (`buchsbaumEisenbud_acyclic`) axiom-clean;
`FlatLocus` openness additionally needs **00ME** (`:118`), **00MI** (`:1156`), **00RB** (`:1138`), **T-REDUCEP**
(`:1176`), **T-FINAL** (`:1200`) — all presently `sorry`, several substantial (00ME is the local flatness
criterion; 00MI/00RB are the fibrewise-criterion cores). So BB-FLAT is gated on **[T-BE-TAIL] + the flat-locus
assembly chain** — a multi-session frontier, not "150–300 LOC". Route B (miracle flatness) is a separate large
mathlib-absent (CM) development; skip. Progress 2026-07-09: 00HM (T-DEVISSAGE) proven axiom-clean; the two
fibre-exactness predicates (`SpecialFibreExact`/`FibreExactAt`) authored — the layer can now at least be stated.
- **BLOCKER TODAY**: [T-BE-TAIL] (fleet-saturation-held) + the fibrewise bridge (T-B6, P3b3, dormant 3d).
- **WHEN UNBLOCKED**: bridge `mulByHom_flat` in a D2 ForMathlib file (import Torsion.lean, prove the `Flat`
  statement via Route A), holder (stream-B) wires it into Torsion.lean:147 with one `exact`. Do NOT edit the held file.
- **Board note for coordinator**: BB-FLAT (D2) and [T-BE-TAIL] (D2) are the SAME dependency chain — closing
  the B–E tail unblocks BB-FLAT directly; they are one arc, best done in the fresh full-budget session when fleet drops.

## Source locators
KM 2.3.1 §2.3 print ~p.45 (verbatim TODO) · EGA IV 11.3.10 (fibrewise flatness) · AK-1 V.3.6 (miracle flatness) ·
Silverman III.6.4(b) / `HasseWeil/.../TorsionGeneralN.lean` (fibrewise `E[N]≅(ℤ/N)²`) · our FlatLocus/Acyclicity/
NoethApprox (Route-A toolbox, 00RB/00MI, done modulo T-BE-TAIL) · board v10.29 / 8724 / 8866 (BB-FLAT = D2).
