# N-07 — Dead positions and insufficient material

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-07` |
| Title | KvK, KBvK, KNvK are dead; KQvK is not |
| Kind | proof / formalization |
| Addresses | `G-1`, `G-4`, `Q-6` |
| Depends on | `N-02`, `N-03` |
| Dependency requirement | Compiled `IsDead` defined semantically (no legal continuation reaches checkmate) |
| Produces | Theorems `dead_KK`, `dead_KBK`, `dead_KNK`, `not_dead_KQK` (planned) |
| Difficulty | moderate: "no checkmate is reachable" is a universal statement over sequences; proof is by an invariant (material can only decrease and the lone pieces cannot mate) |
| Status | stated |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-20: created at seeding |

## Purpose and scope

Sanity checks for Article 5.2.2 and a building block for endgame values: a KQK state in which
Black captures the queen becomes KvK and is drawn. `not_dead_KQK` guards against an over-broad
definition of `IsDead`; `dead_KK` guards against a vacuous one.

Caution (correction `C-2`): "insufficient material" is a sufficient, not a necessary, condition
for a dead position (blocked pawn chains can be dead with much material). Do not define `IsDead`
by material.

## Readiness

Blocked on `N-02`, `N-03`.
