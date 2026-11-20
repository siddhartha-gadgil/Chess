# N-01 — FIDE Laws of Chess (2023): rules to encode

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-01` |
| Title | Source synthesis of the FIDE Basic Rules of Play and automatic draw rules |
| Kind | source synthesis |
| Addresses | `G-1`, `Q-1`, `Q-2`, `Q-3`, `Q-6` |
| Depends on | `S-1` (FIDE Laws of Chess, 2023) |
| Dependency requirement | Exact article text for Articles 1–5, 9.2.3, 9.3 and 9.6 |
| Produces | A list of rule clauses, each mapped to a planned kernel item in `N-02`/`N-03`; the decisions needed in `Q-1`–`Q-3` |
| Difficulty | routine (reading); the hard part is the modelling choices it exposes |
| Status | stated |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-20: created at seeding |

## Purpose and scope

Fix the rule set that "chess" means in this project. In scope: the Basic Rules of Play (FIDE
Articles 1–5) and the draw rules of Article 9 that do not depend on clocks or arbiters. Out of
scope: competition rules (clocks, touch-move, illegal-move penalties, arbiter procedure,
Articles 6–12 except 9.2.3 and 9.6), and chess variants.

## Sources and prior work

`S-1`: FIDE Handbook, *Laws of Chess*, approved by the General Assembly 2022-08-07, in force from
2023-01-01, https://handbook.fide.com/chapter/E012023 (accessed 2026-11-20). Clauses checked
against that page:

| Article | Content (paraphrase; quoted where marked) | Planned encoding |
| --- | --- | --- |
| 1.4 | Aim: put the opponent's king under attack so that the opponent has no legal move ("checkmate") | `N-03` `IsCheckmate` |
| 1.5 | "If the position is such that neither player can possibly checkmate the opponent's king, the game is drawn" | `N-03`, `N-07` dead position |
| 2 | 8×8 board, initial position | `N-02` `initialPosition` |
| 3.1–3.6 | Moves of king, queen, rook, bishop, knight; no jumping except knight; capture by moving onto an opponent piece | `N-02` pseudo-legal move generation |
| 3.7 | Pawn moves: one square; two from the starting rank; diagonal capture; en passant "only legal on the move following this advance"; promotion "must exchange that pawn … for a new queen, rook, bishop or knight of the same colour" | `N-02`; en passant needs last-move information |
| 3.8 | Castling: right lost permanently if the king or that rook has moved; prevented temporarily if the king's square, the square it crosses or its destination is attacked, or if any piece stands between king and rook | `N-02`; castling rights are part of the state |
| 3.9 | Check: king attacked by one or more opponent pieces; "No piece can be moved that will either expose the king of the same colour to check or leave that king in check" | `N-02` legality filter |
| 3.10.3 | "A position is illegal when it cannot have been reached by any series of legal moves" | `Q-3` reachability |
| 5.1.1 | Checkmate wins and ends the game immediately | `N-03` |
| 5.2.1 | Stalemate: player to move has no legal move and is not in check → draw | `N-03` |
| 5.2.2 | Dead position: neither player can checkmate by any series of legal moves → draw | `N-03`, `N-07` |
| 9.2.3 | Positions are the same iff the same player has the move, the same pieces stand on the same squares, and "the possible moves of all the pieces of both players are the same" | `Q-2`: equality of positions is by legal-move sets, so en passant and castling *possibility* counts |
| 9.3 | 50 moves by each player without pawn move or capture: draw **on claim** | `Q-1` |
| 9.6.1 | Same position at least five times: **automatic** draw | `Q-1`, `N-03` |
| 9.6.2 | 75 moves by each player without pawn move or capture: **automatic** draw; checkmate on the last move takes precedence | `Q-1`, `N-03` |

Not yet extracted: the agreed-draw and resignation rules (irrelevant to perfect play); the exact
wording of the threefold-repetition claim (9.2.1–9.2.2), needed only if `Q-1` chooses the
claim-based model.

## Theory development

Observations that drive the kernel design:

1. Legality of a move depends on more than the piece placement: side to move, castling rights,
   en passant target (only on the very next move). These go into the position state (`Q-2`).
2. The automatic draw rules 9.6.1–9.6.2 depend on game history (repetition counts, a halfmove
   clock). Either the state carries a halfmove clock and a repetition table, or the game is
   modelled on histories.
3. Rule 9.2.3 compares positions by their sets of possible moves, not by FEN fields. Two
   positions with a nominal en passant square but no legal en passant capture are the same.
4. Article 1.5 / 5.2.2 (dead position) is a semantic, reachability-based predicate. It is
   well-defined but not obviously decidable cheaply; it should be defined semantically and
   decided only for special material (`N-07`).
5. Without 9.6, the game tree is infinite. With 9.6.2 every play is finite: each window of 150
   plies needs a pawn move or capture, and there are finitely many of those.

## Claims and evidence

- The table above: sourced (S-1), paraphrases checked against the page on 2026-11-20.
- Observation 5: proof sketch (pawn moves at most 8×6 per side plus at most 30 captures, so plies
  are bounded); to be made precise in `N-04`.

## Difficulty, barriers and readiness

No barrier. It becomes complete once `Q-1`–`Q-3` are decided and each row has a named Lean
declaration.

## Outputs and next dependencies

Unblocks `N-02` (board and moves) and `N-03` (outcomes and draw rules).
