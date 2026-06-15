# Reply integration — 2026-05-26 (round 4)

Reply received from senior algebraic geometer / Huber–Wedhorn expert on
2026-05-26.

- Brief: `../2026-05-26-2/brief.md`
- Reply: `../2026-05-26-2/reply.md`

## Interpretation summary

11 substantive reviewer points across the 6 brief questions + the empty-cover
side issue + concrete implementation guidance. **Zero unanswered Qs** —
reviewer covered everything.

Key strategic answers:
- **Q1/Q2**: Do NOT add `[SigmaCompactSpace A]` or `[SeparableSpace A]` to
  the keystone. The narrowing is unacceptable for adic-space examples like
  `ℂ((t))`-affinoids.
- **Q3**: Build a **Tate-absorbing** Baire OMT (not bare Bourbaki — that
  general form is shaky, counterexample: discrete → coarser-complete
  identity). Reviewer supplied a schematic Lean signature and 7-step proof
  outline.
- **Q3(i)/Q3(ii)**: No existing formal proof; the Tate form is solid where
  the bare topological-group form is not.
- **Q4**: Tate-absorbing OMT is the right route; direct metric/Stacks/Wedhorn
  6.18 alternatives are viable but more work or less reusable.
- **Q5**: Route B contingency priority: Cor 7.32 finset → strengthened
  L1 → σ-walk last. Don't resume Route B now.
- **Q6**: Clean Lean re-proof by OMT; document the bridge in plain English.

Unprompted but actionable:
- `presheafValue_sigmaCompactSpace` should be off the keystone path.
- Empty-cover residual should not be a hidden unprovable branch in the
  final clean theorem.

## Changes applied

### 4 NEW tickets

- **T-ROUTE-C-OMT** — Tate-absorbing Baire open mapping theorem. New
  theorem `IsOpenMap.of_surjective_tate_absorbing` in `BanachOMT.lean`
  per reviewer's schematic signature + 7-step proof outline. All sub-lemmas
  already sorry-free in BanachOMT.lean; only main assembly missing.
- **T-ROUTE-C-WIRE** — wire the new OMT into `productRestrictionSubToEqualizer_isOpenMap`
  replacing the mathlib sigma-compact dependency.
- **T-ROUTE-C-SEPARABLE-COROLLARY** (LOW priority) — optional
  `isSheafy_ofStronglyNoetherianTate_of_separable` shortcut for
  ℚ_p-affinoid applications.

### 2 MODIFIED tickets

- **T-ROUTE-C-5** (`presheafValue_sigmaCompactSpace`) — status changed
  from "B2" to "SUPERSEDED by T-ROUTE-C-OMT". Lemma no longer on
  keystone path; retained as optional separated lemma at most.
- **T-ROUTE-C-7** (`productRestrictionSub_isInducing_tate_empty`) —
  marked PARTIAL with TO BE CLEANED PER ROUND-4 flag. Two cleanup options
  documented (carry typeclasses locally OR add Nonempty precondition).

### Documentation changes applied

- **Keystone docstring** in `StructureSheaf.lean` (`productRestrictionSub_isInducing_tate`):
  added Round-4 bridge paragraph ("Wedhorn proves algebraic equalizer
  exactness; topological-ring sheaf condition follows because the bijection
  is continuous surjective between complete Tate objects, hence open by
  Tate-absorbing OMT") + Note documenting the sigma-compact ⇒ Tate-absorbing
  switch + currently transitive sub-lemma sorry pending T-ROUTE-C-WIRE.
- **`.mathlib-quality/decomposition.md`**: Added Round-4 update section
  under "Locked policy" documenting the keystone-signature pristine
  decision, the Tate-absorbing OMT route, the Route B fallback priority,
  and the empty-cover cleanup flag.

## Changes rejected by user

(none — full approval)

## Open questions remaining

None — reviewer covered all six brief questions plus the unprompted
side-issue.

## Decisions recorded but not actioned

- The keystone signature stays exactly as Wedhorn 8.28(b) states it
  (no extra typeclass beyond `[IsTateRing A] [IsNoetherianRing A]
  [IsStronglyNoetherian A] [T2Space A] [NonarchimedeanRing A]`).
- Route B is fallback only; no resumption at this time.
- `T-ROUTE-C-OMT` and `T-ROUTE-C-WIRE` are the active path to closing
  the keystone fully.