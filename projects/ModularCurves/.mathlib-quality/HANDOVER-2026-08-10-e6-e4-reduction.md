# HANDOVER 2026-08-10 — AP-E6 complete; `_self` reduced to the single E4a box

**Session summary (continuation of the 2026-08-09 DS4 session, same branch
`dev/modular-curves`).** Everything below is pushed through `f7ad643ed`, full tree green
at **9778 jobs**, every new declaration axiom-clean (propext, Classical.choice,
Quot.sound).

## What landed today (after the AP-E1/E2/E3 arc of the previous handover)

### 1. AP-E6 COMPLETE — `weilPairingEval_mul` PROVED (register T-C2b)
KM 2.8.4.1 at `π₁ = [N], π₂ = [M]` needs **no dual-isogeny machinery**: every isogeny in
sight is a self-dual `mulByN`. New file `WeilPairing/KMCompatibility.lean`:
- `mulByN_comp` (`[N] ≫ [M] = [N·M]`, from `mulBy_comp` in
  `EllipticCurve/EndomorphismDegree.lean` — NOT in the KMNaturality closure; the
  Moduli/GammaH twin `mulByHom_comp_mulByHom` is the wrong import direction, cleanup-fleet
  note),
- torsion glue (`mem_torsionPoints_mul_right`, `smul_mem_torsionPoints_of_mul`),
- `hM_mulByNPullback` / `hnorm_mulByNPullback` — the `[M]`-pulled dataset is a
  `κ(M•Q)`-dataset (`kappa_nsmul` + `picMap_mulByHom_kappa_pow` (★);
  `zero_comp_mulByHom_baseChange` + `mem_sectionUnits_pullback`),
- `torsionSplittingEval_mulByN_pullback` — **the CORE**: `weilPairingKM`'s dataset is
  level-independent, and `[N]⁻¹([M]⁻¹W) = [N·M]⁻¹W` makes the `N·M`-level normalised
  splitting family literally an `N`-level family for the pulled dataset (pin via
  `eq_torsionSplittingEval`; transport is `resUnit`/`unitPullback`-calculus only),
- `weilPairingKM_mul_smul_right` (`e_{N·M}(P,Q) = e_N(P, M•Q)`), `asSection_zsmul`
  (two `map_zsmul`s — both layers of `asSection_eq_baseChangeEquiv_symm` are additive).
- `Basic.lean:491` `weilPairingEval_mul` filled: bridge ×2 + E6-e + `weilPairingKM_congr`
  at `asSection_zsmul`/`natCast_zsmul` + the proved `weilPairingEval_nsmul_right`.

### 2. `[N] : E ⟶ E` SURJECTIVE over an arbitrary base, every characteristic
New file `EllipticCurve/MulByHomSurjective.lean` — the BETA transport of the any-field
model surjectivity (`mulByHom_surjective`, MulByHomDegree), sibling of the finite-fibres
transport. Instance pack at the model over `κ(s)`: `modelMulByHom_locallyQuasiFinite_of_field`
+ IsProper-via-`mulByHom_π` + `IsFinite.of_isProper_of_locallyQuasiFinite` +
`mulByHom_flat` (BB-FLAT, already in-tree and axiom-clean) +
`LocallyOfFiniteType.isLocallyNoetherian` at `π` feeding mathlib's low-priority lft⟹lfp
instance.

### 3. AP-E4 (`weilPairingEval_self`) reduced to ONE box
New file `WeilPairing/AlternationReduction.lean`:
- `weilPairingEval_self_of_halving` — KM Notes-on-Ch.2 chain
  `e_N(x,x)|_{T'} = e_N(2P,2P) = e_{N·2}(2P,P) = e_{N·2}(P,P)² = 1` over any
  `Γ`-injective halving cover. **Uses only proved laws** (restrict, bridge + E6-e mixed
  shift, `add_left` at `2P = P + P`). `zsmul_left`/`antisymm` deliberately avoided —
  they derive from `_self` (circular).
- `weilPairingEval_self_of_halving_of_flat` — `hinj` discharged by the in-tree WP-C1
  (`DescentFaithful.injective_appTop_of_flat_of_surjective`).
- `weilPairingEval_self_of_forall_diag_sq` — **the halving cover exists
  unconditionally**: `[2]` flat + surjective ⟹ the `[2]`-fibre product over `x` is a flat
  surjective cover; its tautological half-point is `N·2`-killed by pure composition
  algebra (`mulBy_comp`; no Point-smul). So `_self` follows from the universal diagonal
  square `∀ T'' g'' P hP, e_{N·2}(P,P)² = 1` **alone**.

## Register state (`WeilPairing/Basic.lean`, 2 sorries)
- `weilPairingEval_self` (`:372`) — remaining content = **AP-E4a**: the diagonal square
  `e_M(P,P)² = 1` (KM 2.8.3's alternation instance, cited to [Oda]). Biextension/cube
  -theoretic; bilinearity provably cannot reach it (symmetry information). When it lands,
  `_self := weilPairingEval_self_of_forall_diag_sq` closes immediately (the wiring cannot
  live in Basic.lean — import direction — so fill `_self`'s sorry from the reduction at
  that point, or move the reduction upstream then).
- `weilPairingEval_nondegenerate` (`:435`) — **AP-E5**: Cartier–Nishi (2.8.2.1), also
  [Oda]. Its own sub-development.

Both are research-scale. `weilPairingEval_symplectic` (11 Rho call sites) inherits
sorryAx only through `_self`.

## Do-not-touch (unchanged from 2026-08-09)
`evalGenerator_mem_nonZeroDivisors`, `relEffCartierDiv_of_degreeOne_package` — FALSE AS
STATED, owner decision pending (b2_log). AP-D4 `⊇` downstream. The route-A `WP-*`/AP-D3
strands in the ticket file predate the D7 decision — superseded; do not resurrect without
an owner call.

## Lean lessons of the day (also on the board, with the tickets)
1. calc whose head TERM is a multiline application mis-parses ("true : Bool" calc error)
   — refine-`Eq.trans` chains instead.
2. `congrArg (Scheme.resUnit _)` across defeq-equal opens makes goals "not type-correct
   under implicit transparency"; `rw [map_mul]` then refuses — close with term
   applications (`(map_mul _ _ _).trans`, `congrArg₂ (· * ·)`,
   `(resUnit_resUnit …).trans (resUnit_resUnit …).symm` through the proof-irrelevant
   middle).
3. `rw [← mulByHom_π]` in a goal mentioning a `Point` breaks the motive (bare `E.π` is in
   the subtype's type) — calc with `congrArg (c ≫ ·)` legs.
4. After `apply hinj` the goal can carry implicit-transparency damage — same remedy.
5. `pow_two`, not `sq`, is `a^2 = a*a`.
6. FD-exhaustion ("Too many open files in system") struck 4× today — always retry before
   diagnosing.
