# N-10 — King and rook versus king

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-10` |
| Title | KRK is a forced win for White to move, within 16 moves |
| Kind | computation / certificate / formalization |
| Addresses | `G-4` |
| Depends on | `N-02`, `N-03`, `N-05` (KQK pipeline: `KQKCheck` generic lemmas) |
| Dependency requirement | Compiled rules kernel, `ForcesMate`, `mem_legalMoves_of`, `ForcesMate.halfmove`, `sqOf_kqkIdx` |
| Produces | `Certificates/Chess/{KRKCheck,KRKData,KRKBridge,KRK}.lean`, `KRKChunks/C00…C63.lean`; theorem `krk_forcesMate_wellFormed` (planned) |
| Difficulty | moderate (pipeline reuse); cost ≈ 8 CPU-hours of kernel checking |
| Status | **verified** (White to move, Black to move, full game) |
| Implementation status | complete |
| Implementation evidence | `notes/reasoning/2026-11-24-krk/` (oracle `kxk_retro.py R`, validator `kxk_validate.py R`, generator `gen_krk_cert.py`); `KRKCheck.lean` (compiled, warning-free); `KRKData.lean` (compiled) |
| Lean evidence | `LeanTheory.Chess.{krk_forcesMate_wellFormed, krk_black_to_move, krk_game_whiteWins_wellFormed}` (axioms: `propext`, `Classical.choice`, `Quot.sound`); supporting `krk_table_sound`, `krk_forcesMate_of_table_wellFormed`, `krk_black_to_move_of_table`, `krk_game_whiteWins_of_table_wellFormed`, `krkTable_ok`, `krk_row_<wk>_<wr>` (4096 kernel checks) |
| Audit evidence | 2026-11-24: statements reviewed; full build warning-free; axiom audit passed (16 558 declarations) |
| Last updated | 2026-11-24: all 64 chunks pass (≈ 9.5 min each, 5 parallel, 3.5 GB caps); KRK theorems compiled |

## Results so far

Numerical observations (untrusted oracle, validated by an independent script, 0 errors):

- 175 168 well-formed White-to-move KRK states (21 959 up to symmetry), **all forced wins**;
  maximum depth **16** White moves (agrees with the commonly cited KRK maximum).
- Depth distribution 1…16: 1512, 4676, 3852, 1900, 4848, 8708, 11320, 17172, 20088, 19016,
  20476, 21480, 17824, 16136, 5244, 916.
- Black to move (223 944): 22 176 can capture an undefended rook (draw), 68 stalemates, 216
  already mated, 201 484 mate in n ≤ 16.

Compiled: `krk_table_sound` (if every entry passes `krkStateOK`, every entry of depth `d` is a
forced mate within `d` moves). Entries are 32-bit: depth (5 bits), source and destination.
The checker is a rook copy of the KQK checker (`KQKCheck`), reusing its piece-independent lemmas;
unifying the two over the piece kind is possible future cleanup.

## Results (compiled)

- `krk_forcesMate_wellFormed`: every well-formed KRK position with White to move and no castling
  rights is a forced mate within 16 moves.
- `krk_black_to_move`: with Black to move, Black is mated, stalemated, can capture an undefended
  rook into a dead position, or White forces mate within 16.
- `krk_game_whiteWins_wellFormed`: in `chessGame` (all automatic draw rules) from a fresh start
  with clock ≤ 118, White wins and the value is `whiteWins`.

Not proved: that 16 is attained (observation only); KRK fixtures for the Black-to-move cases.
Possible cleanup: one checker generic over the piece kind instead of the KQK/KRK copies.
