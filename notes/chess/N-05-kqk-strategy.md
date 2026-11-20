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
| Status | stated |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
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

## Claims and evidence

- "KQK White to move is always a win": sourced computational observation (tablebases), not yet
  proved here.
- "Maximum depth 10": commonly cited; unconfirmed (`Q-4`).

## Difficulty, barriers and readiness

Blocked on `N-02`, `N-03`. Main risk: kernel evaluation cost of checking tens of thousands of
positions with a naive move generator. `N-06` estimates the size and the depth profile first.

## Outputs and next dependencies

Becomes the template for KRK, KBBK, KBNK (`G-4`).
