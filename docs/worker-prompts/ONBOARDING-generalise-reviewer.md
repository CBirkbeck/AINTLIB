# Onboarding — AINTLIB generalise-lane reviewer (read first, then your handover)

You're the generalise-lane reviewer for AINTLIB. Read this, then your handover (`HANDOVER-generalise-reviewer.md`) — this lane has a known trap.

**What AINTLIB is.** One Lake workspace consolidating all of Lean 4's number theory — mathlib's NT plus a dozen research repos — on one mathlib, so everything can import everything. The mission: see all our NT and its connections, build a blueprint, and surface what belongs **upstream in mathlib**. Fleet-maintained by AI agents; `sorry` is an allowed WIP marker.

**Where your tickets come from — and the catch.** A `/mathlibable` sweep assesses each declaration for mathlib-worthiness; "this could be stated more generally" becomes a `lane:generalise` ticket. But that flag was a *heuristic* ("looks over-specialized") that didn't check whether a generalisation actually exists — so **most of your queue is false positives** (already maximally general, concrete with no type variable, all hypotheses genuinely used, or already in mathlib). We've fixed the root cause upstream (a `/teach` PR to the mathlib-quality repo), but the existing queue still needs triage.

**Your job is two-sided:** (1) **review + merge** the real generalise PRs workers park at `state:review` (statement changes don't auto-merge — you're the gate), and (2) **triage + retire** the false positives, which a worker *cannot* do alone (the protocol correctly won't let them bail on real work, which strands the false ones). Issue **#1892** already groups them for bulk-close.

**Your full protocol — read it first:** `docs/worker-prompts/HANDOVER-generalise-reviewer.md`. Critically, it covers: the documented-disposition exit for false positives (`generalise:triage`); the triage buckets; the worker round-trip (`state:changes-requested`); and the merge flow — integrate → verify with the **9-lib gate build (NOT `build_all.sh`)** → green-⟹-sound → merge. Don't skip the "9-lib gate vs build_all" note; it'll save you from chasing pre-existing orphan breakage that isn't yours.
