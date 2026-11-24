# N-05 — King and queen versus king: a proved winning strategy

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-05` |
| Title | KQK is a win for the side with the queen |
| Kind | research approach / proof / certificate |
| Addresses | `G-2`, `Q-4`, `Q-8` |
| Depends on | `N-02`, `N-03`; informed by `N-06` |
| Dependency requirement | `N-02`/`N-03` compiled: `legalMoves`, `IsCheckmate`, `ForcesMate`; `N-06` supplies untrusted data only |
| Produces | Theorem `kqk_forcesMate` (planned): for every KQK state `s` with White to move, Black not in check, kings not adjacent, `ForcesMate White N s` for an explicit `N` (target `N = 10`); a Black-to-move corollary |
| Difficulty | moderate–hard: about 28 000–40 000 relevant positions (`S-6`, order of magnitude only); a pure hand proof has many cases |
| Status | **verified** (White to move; see scope) |
| Implementation status | complete (White to move); Black-to-move case split and game-state transfer not started |
| Implementation evidence | `LeanTheory/Certificates/Chess/{KQKCheck,KQKData,KQKBridge,KQK}.lean`, `KQKChunks/C00…C63.lean`; generator `notes/reasoning/2026-11-20-kqk-oracle/computations/gen_lean_cert.py` |
| Lean evidence | `LeanTheory.Chess.kqk_forcesMate`, `LeanTheory.Chess.kqk_forcesMate_wellFormed` (axioms: `propext`, `Classical.choice`, `Quot.sound`); supporting `table_sound`, `kqk_forcesMate_of_table`, `kqk_forcesMate_of_table_wellFormed`, `play_kqk_king/queen/black`, `ForcesMate.halfmove`, `kqkTable_ok`, `chunkOK_all`, `kqk_row_<wk>_<wq>` (4096 kernel checks) |
| Audit evidence | 2026-11-24: statements reviewed; full build warning-free; axiom audit passed (11 648 declarations) |
| Last updated | 2026-11-20: created at seeding |

## Purpose and scope

Precise target (`G-2`). Let a *KQK state* be a position whose only pieces are a white king, a
white queen and a black king, on distinct squares, with no castling rights or en passant target,
that is *well formed*: the side not to move is not in check, so the kings are not adjacent.

1. **White to move:** for every such state, `ForcesMate White N s`. Commonly cited maximum depth
   to mate for KQK is 10 moves (`S-6`, unconfirmed; to be checked by `N-06`).
2. **Black to move:** if Black has a legal move and cannot capture the queen, White forces mate;
   if Black can capture an undefended queen, the result is K vs K (dead, draw); if Black has no
   legal move, the result is checkmate or stalemate. A precise case split is part of this note.

The statement quantifies over well-formed states, not over FIDE-reachable ones (`Q-3`). This
makes the theorem stronger, since every reachable KQK position is well formed.

## Approaches

**(a) Human strategy (user idea `U-1`, `U-2`).** Drive the black king to an edge with the queen
a knight's move away ("box" shrinking), bring the white king up, mate on the edge, and before every
queen move check that Black still has a legal move (avoid stalemate). Proof needs a potential
function (box area, king distance) that strictly decreases within bounded moves, plus a stalemate
lemma. Gives insight and generalises to KRK; long case analysis.

**(b) Certificate (retrograde analysis).** An untrusted program (`N-06`) computes, for every
state, a depth and a white move. Lean checks the certificate by kernel evaluation: for each state
of depth `d` the given move is legal and every black reply is either checkmate-in-0 or a state of
depth `< d`. A soundness theorem turns the check into `ForcesMate`. Mechanical, scalable to other
endgames, but needs efficient computable move generation and an efficient indexed table.

**(c) Hybrid.** Use symmetry (8-fold board symmetry with no pawns) to cut the table, and the
certificate only for the core; hand lemmas for symmetry soundness.

Recommendation: (b) with (c) symmetry, as it reuses the `Certificates/` tooling and gives the exact
depth. Keep (a) as a separate, more explanatory theorem if wanted.

## Sources and prior work

- `S-6`: endgame tablebase literature (e.g. Wikipedia "Endgame tablebase", chessprogramming.org
  "Endgame Tablebases"). KQK depth figures there are computational observations, not proofs.
- User ideas `U-1` ("trap kings against the end"), `U-2` ("guard against stalemates").

## Result (compiled)

```lean
theorem kqk_forcesMate_wellFormed (p : Position) (wk wq bk : Square) (h₁ : wk ≠ wq)
    (h₂ : wk ≠ bk) (h₃ : wq ≠ bk) (hb : p.board = kqkBoard wk wq bk) (ht : p.turn = .white)
    (hcr : p.castling = .none) (hw : wellFormed p = true) : ForcesMate .white 10 p
```

Every well-formed position whose pieces are a white king, a white queen and a black king, with
White to move and no castling rights, is a forced checkmate for White within 10 moves against
every defence (any halfmove clock). `kqk_forcesMate` states the same for `kqkPos` with the
hypothesis "black king not attacked".

Method (route (b)): the untrusted oracle (`N-06`) gives a depth and a White move for each of the
262 144 square triples; `stateOK` checks one entry (White's move is in the piece's move list, does
not capture and leaves White's king safe; Black is mated, or every legal Black reply is a
non-capturing king step to an entry of smaller nonzero depth); `coverOK` checks that every valid
triple has an entry. The kernel evaluates these in 4096 declarations (`kqk_row_wk_wq`, 64 per
chunk file; ≈ 8 min per chunk, 5 chunks in parallel under a 3.5 GB cap each, ≈ 1.8 h wall);
`table_sound` turns the check into `ForcesMate` by strong induction on the depth, using symbolic
lemmas for the effect of king and queen moves on KQK boards.

Scope and limits:

- White to move only. The Black-to-move case split (mate unless Black can capture an undefended
  queen or is stalemated) is not yet a theorem.
- `ForcesMate` is about positions: it ignores history-dependent draws. Transfer to `GameState`
  (75-move and fivefold rules) needs a lemma: at most 19 plies are needed and the depth strictly
  decreases along the forcing line, so no position repeats within it; open.
- Castling flags are assumed `none` (they are meaningless without rooks; generalising needs a
  lemma that castling flags without rooks do not affect legal moves).
- Depth 10 is the bound proved; that it is attained (exactness) is not proved here.
- Symmetry was not used: all 144 508 White-to-move states were checked directly.

## Claims and evidence

- "KQK White to move is always a win": sourced computational observation (tablebases), not yet
  proved here.
- "Maximum depth 10": commonly cited; unconfirmed (`Q-4`).

## Difficulty, barriers and readiness

Blocked on `N-02`, `N-03`. Main risk: kernel evaluation cost of checking tens of thousands of
positions with a naive move generator. `N-06` estimates the size and the depth profile first.

## Outputs and next dependencies

Becomes the template for KRK, KBBK, KBNK (`G-4`).
