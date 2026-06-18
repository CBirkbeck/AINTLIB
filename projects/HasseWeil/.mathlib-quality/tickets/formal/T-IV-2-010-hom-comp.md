# T-IV-2-010: FormalGroupHom composition

**Status**: REVIEW
**Silverman**: IV.2 (category structure on formal groups)
**Module**: `HasseWeil/FormalGroup/Hom.lean`
**Owner**: worker-G (via subagent)
**Estimated lines**: 80
**Difficulty**: medium (subst_comp_subst bookkeeping)
**Stream**: D

## Depends on
- T-IV-2-002 (FormalGroupHom) — DONE
- T-IV-2-006 (mulByNatHom) — DONE (ℕ)

## Blocks
- Downstream results needing composition of formal group homs (e.g., height
  of compositions, Silverman IV.4.6).

## Statement

Define composition of formal group homomorphisms:
```lean
def FormalGroupHom.comp {F G H : FormalGroup R}
    (g : FormalGroupHom G H) (f : FormalGroupHom F G) : FormalGroupHom F H
```
with underlying series `PowerSeries.subst f.toSeries g.toSeries` (the usual
power-series composition).

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

noncomputable def FormalGroupHom.comp {F G H : FormalGroup R}
    (g : FormalGroupHom G H) (f : FormalGroupHom F G) : FormalGroupHom F H

@[simp] theorem FormalGroupHom.comp_toSeries {F G H : FormalGroup R}
    (g : FormalGroupHom G H) (f : FormalGroupHom F G) :
    (g.comp f).toSeries = PowerSeries.subst f.toSeries g.toSeries

theorem FormalGroupHom.id_comp (f : FormalGroupHom F G) :
    (FormalGroupHom.id G).comp f = f

theorem FormalGroupHom.comp_id (f : FormalGroupHom F G) :
    f.comp (FormalGroupHom.id F) = f

theorem FormalGroupHom.comp_assoc ...

end HasseWeil.FormalGroup
```

## Notes
- The `toSeries` and `zero_const` parts are routine (use
  `HasseWeil.FG.constantCoeff_univariate_subst`).
- The `preserves_add` part requires **two applications** of
  `MvPowerSeries.subst_comp_subst_apply`: once on each side, nesting
  `f.preserves_add` inside `g.preserves_add`. The bookkeeping is mechanical
  but tedious (~50 lines). See the released attempt in git history for the
  earlier version of `Hom.lean` (removed because `unfold_let` isn't
  available in the current toolchain).

## Progress log
- 2026-04-17T20:00Z [auto] Added ticket while setting up FormalGroupHom API
  (T-IV-2-002 follow-up). `FormalGroupHom.id` and `FormalGroupHom.ext` are
  done in `Hom.lean`; composition deferred to this ticket.
- 2026-04-17T20:15Z [worker-G] Attempted. Structured the proof via:
  1. `PowerSeries.subst_comp_subst_apply` on LHS (twice nested subst → outer).
  2. Apply `f.preserves_add` to simplify inner.
  3. Commutation helper: `PowerSeries.subst (MvPowerSeries.subst A B) g =
     MvPowerSeries.subst A (PowerSeries.subst B g)` — **added this helper to
     `Hom.lean` as public lemma `PowerSeries_subst_MvSubst_eq`**.
  4. Apply `g.preserves_add`.
  5. Collapse via `MvPowerSeries.subst_comp_subst_apply` on outer H substitution.
  6. Show `funext` equivalence: each entry of the vector matches the target.
  Stuck at step 6: `rw` chain leaves goal in form `MvPowerSeries.subst (fun x ↦
  MvPowerSeries.subst ... f.toSeries) g.toSeries` which doesn't syntactically
  match what I expected. Some `PowerSeries.subst` calls unfolded to
  `MvPowerSeries.subst (fun _ => ...)` and others didn't, leading to partial
  reduction that breaks the final matching step.
  **Recommended for future worker**: use `MvPowerSeries.substAlgHom` directly
  (pass through the AlgHom structure) rather than manipulating `subst` with
  `rw`. The identity `g ∘ f` corresponds to `substAlgHom g ∘ substAlgHom f
  = substAlgHom (substAlgHom g f)` which is `substAlgHom_comp_substAlgHom`
  in mathlib (line 369 of `PowerSeries/Substitution.lean`).
  Released; the helper `PowerSeries_subst_MvSubst_eq` is ready for reuse.
