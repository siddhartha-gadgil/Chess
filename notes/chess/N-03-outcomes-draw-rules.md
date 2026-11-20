# N-03 — Kernel: game outcomes, draw rules and the game as a finite game

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-03` |
| Title | Checkmate, stalemate, dead position, automatic draws; the game tree |
| Kind | definition / formalization |
| Addresses | `G-1`, `G-3`, `Q-1`, `Q-6` |
| Depends on | `N-01`, `N-02` |
| Dependency requirement | `N-02` compiled (`legalMoves`, `inCheck`, `play`); `Q-1` decided |
| Produces | `IsCheckmate`, `IsStalemate`, `IsDead`, `Outcome` (`whiteWins / draw / blackWins`), a game-state type with history and terminal predicate; contract predicates `ForcesWin`, `ForcesAtLeastDraw` |
| Difficulty | moderate: the rule model (`Q-1`) changes the game; dead position is a reachability predicate |
| Status | stated |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-20: created at seeding |

## Purpose and scope

Define what it means for a game to end and who wins, and the strategy notions used by the goals.

Contracts (separate predicates, see `00-model-contracts.md`):

- `ForcesMate (c : Color) (n : ℕ) (s : State)`: player `c` has a strategy such that, against
  every reply, a checkmate of the opponent occurs within `n` moves of `c`, before any automatic
  draw. Defined inductively on `n` (an AND–OR tree), so it is computable for fixed small positions.
- `ForcesAtLeastDraw (c) (s)`: `c` has a strategy that never loses.
- `GameValue (s) : Outcome`: defined only once determinacy (`N-04`) is proved.

Rule models (`Q-1`), to be fixed before `G-3` is stated:

| Model | Terminal conditions | Remarks |
| --- | --- | --- |
| **A. FIDE automatic** | checkmate, stalemate, dead position, fivefold repetition (9.6.1), 75-move rule (9.6.2) | Finite game; closest to the Laws without claims |
| B. FIDE with claims | A plus optional draw moves for 9.2 (threefold) and 9.3 (50-move) | Rational players claim whenever behind; value may differ from A |
| C. Idealised | checkmate, stalemate, any repetition = draw, no move-count rule | Standard in game theory and tablebases (DTM without 50-move rule) |

For KQK (`G-2`) the choice is immaterial if a mate within 10 moves is proved, as no draw rule can
interfere within 10 moves from a fresh history. The choice matters for `G-3`: some tablebase
wins need more than 50 moves without a capture or pawn move ("cursed wins"), so models A/B/C can
give different values for such positions.

## Dependencies

`N-02` (compiled kernel required). `Q-1` decision.

## Sources and prior work

`S-1` Articles 1.4, 1.5, 5.1–5.2, 9.2.3, 9.3, 9.6.

## Claims and evidence

None yet.

## Difficulty, barriers and readiness

Blocked on `N-02`. `IsDead` should be defined semantically (no sequence of legal moves leads to a
checkmate by either side) and proved for special material in `N-07`; it should not be replaced by a
material-count heuristic, which is only a sufficient condition.

## Outputs and next dependencies

Unblocks `N-04` (instantiation), `N-05`, `N-07`.
