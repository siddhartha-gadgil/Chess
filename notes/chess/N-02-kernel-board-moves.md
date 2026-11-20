# N-02 — Kernel: board, position and legal moves

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-02` |
| Title | Lean kernel for squares, pieces, positions and legal moves |
| Kind | definition / formalization |
| Addresses | `G-1`, `Q-2` |
| Depends on | `N-01` |
| Dependency requirement | `N-01` stated (rule list); `Q-2` decided (state contents) |
| Produces | `LeanTheory/Kernel/Chess/*.lean` (planned): `Square`, `Piece`, `Color`, `Position`, `Move`, `pseudoMoves`, `inCheck`, `legalMoves`, `play`, `initialPosition`; sanity file `LeanTheory/Sanity/Chess/*.lean` |
| Difficulty | moderate: many cases (castling, en passant, promotion), and the definitions must be computable in the Lean kernel so that sanity checks and certificates can run by evaluation |
| Status | verified (for the scope below; see audit findings A-1…A-3) |
| Implementation status | complete (first version) |
| Implementation evidence | `LeanTheory/Kernel/Chess/Rules.lean`, `LeanTheory/Sanity/Chess/Rules.lean` |
| Lean evidence | Kernel: `LeanTheory.Chess.{Square, sq, Square.shift, Board, CastlingRights, Position, Move, attackedBy, inCheck, pseudoMoves, castlingMoves, play, legalMoves, isLegal, isCheckmate, isStalemate, playLegal, perft, initialPosition}`. Sanity: `LeanTheory.Sanity.Chess.{perft_one, perft_two, perft_three, foolsMate_checkmate, initial_not_checkmate, stalemate_fixture, stalemate_needs_turn, castle_legal, castle_moves_rook, castle_through_check, castle_after_king_moved, enPassant_legal, enPassant_removes_pawn, enPassant_expires, promotion_four, pinned_bishop_pseudo, pinned_bishop_no_moves}` |
| Audit evidence | 2026-11-20 audit of the working tree on `e644cf8` (implementation plan §4) |
| Last updated | 2026-11-20: kernel and sanity suite compiled; build warning-free; axiom audit passed |

## Purpose and scope

Encode FIDE Articles 2–3 as **computable definitions**, not as laws: the rules of chess are a
definition of a game, so there is no empirical law and no typeclass is needed for them. The
"model" risk is instead *fidelity*: does `legalMoves` equal the FIDE set of legal moves? That is
checked by sanity tests, not assumed.

Proposed state (`Q-2`, pending decision): piece placement (`Square → Option (Color × PieceType)`
or an array of 64), side to move, four castling-right flags, optional en passant target square,
halfmove clock. Repetition history is kept outside the position (in `N-03`).

Design constraints:
- Squares as `Fin 8 × Fin 8` or `Fin 64`; directions as small integer offsets with bounds checks.
- Everything `def` (not `noncomputable`), so that `eval_cert`/`bool_cert` checks run in the
  kernel (see `lean-proofs`); no `decide`.
- `legalMoves p` = pseudo-legal moves `m` with `¬ inCheck (play p m) p.sideToMove`, plus the
  castling conditions of 3.8.2.2 (king not in check, crossing square not attacked).

## Dependencies

`N-01` (sourced rule list). No compiled dependency.

## Sources and prior work

- `S-1` (FIDE Laws).
- `S-3` (perft reference counts) for regression tests. The commonly used start-position counts are
  perft(1) = 20, perft(2) = 400, perft(3) = 8 902, perft(4) = 197 281. These are widely
  reproduced by engines; record a precise source locator before relying on them as fixtures.

## Theory development

Planned sanity suite (the "triad" adapted to definitions, plus risk-specific checks):

| Risk | Check |
| --- | --- |
| Concrete instance | `legalMoves initialPosition` has 20 elements |
| Global regression | perft(2) = 400, perft(3) = 8 902 from the start (by kernel evaluation) |
| Castling through check | A position where the f1 square is attacked: `O-O` is not legal |
| Castling rights | After the king moves and returns, castling is not legal |
| En passant timing | Legal immediately after the double step, illegal one move later |
| Promotion | A pawn reaching the last rank yields exactly four moves per destination (Q, R, B, N) |
| Pinned piece | A pinned piece cannot leave the pin line |
| Checkmate | After Fool's mate (1. f3 e5 2. g4 Qh4#), White is to move, has no legal move and is in check |
| Stalemate | A standard stalemate position: no legal move, not in check |
| Counterexample | A move that leaves one's king in check is excluded |
| Fixtures | Replay of real games from PGN (`N-09`): every move is in `legalMoves` |

## Claims and evidence

- Compiled: the computed counts perft(1) = 20, perft(2) = 400, perft(3) = 8 902 from
  `initialPosition` agree with the standard values (`S-3`), by kernel evaluation (`kernel_fact`,
  no `decide`). Negative control: `perft 1 initialPosition = 21` and the illegal move `e1–e3` are
  rejected by the kernel.
- Compiled fixtures for checkmate, stalemate, castling (legal, through check, after the king
  moved, rook placement), en passant (legal, removes pawn, expires), promotion (four choices) and
  pins (pseudo-legal but not legal), as listed in the Lean evidence.
- **Fidelity is evidence, not proof**: the claim "`legalMoves` equals the FIDE legal-move set" is
  supported by these fixtures, not proved; there is no formal FIDE text to prove it against.

Scope notes (audit):

- `A-1` (medium): functions are total on ill-formed positions. With no king, `inCheck` is
  `false`, so such a position can never be checkmate. Theorems such as `G-2` must assume a
  well-formedness predicate (one king per side, side not to move not in check, no pawns on the
  first/last rank); `Position.WellFormed` is to be defined in `N-03`.
- `A-2` (low): `epTarget` is set after every double step (FEN convention), even when no en passant
  capture is possible. FIDE 9.2.3 compares positions by their possible moves, so the repetition
  test in `N-03` must not compare `epTarget` fields directly.
- `A-3` (low): an en passant move is generated whenever `epTarget` matches, without checking that
  an opponent pawn stands behind it. This is correct on positions reached by `play`, but not on
  hand-built positions with an inconsistent `epTarget`; well-formedness should include it.
- Added (`LeanTheory/Sanity/Chess/SpecialMoves.lean`, 23 theorems, sub-agent, all passing with
  no kernel discrepancy): White and Black queenside/kingside castling incl. the classic `b1`
  attacked-but-empty case, castling right lost on rook capture, Black promotion and promotion by
  capture, Black en passant, double check (only king moves), kings not adjacent, no capture of a
  defended piece, and Kiwipete perft(1) = 48, perft(2) = 2039 (source:
  https://www.chessprogramming.org/Perft_Results, Position 2).
- Still missing: recorded-game replay (`N-09`).

## Difficulty, barriers and readiness

First version done (`Q-2` default adopted). Main cost: making perft(3)
evaluate in the kernel in reasonable time; may need efficient data structures (bitboards via
`UInt64`) later. Start with a clear reference implementation; optimise behind a proved
equivalence only if certificates need it.

## Outputs and next dependencies

Unblocks `N-03`, `N-05`, `N-07`, `N-09`.
