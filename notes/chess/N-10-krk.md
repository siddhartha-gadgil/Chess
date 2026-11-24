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
| Status | stated / certificate check running |
| Implementation status | in progress |
| Implementation evidence | `notes/reasoning/2026-11-24-krk/` (oracle `kxk_retro.py R`, validator `kxk_validate.py R`, generator `gen_krk_cert.py`); `KRKCheck.lean` (compiled, warning-free); `KRKData.lean` (compiled) |
| Lean evidence | `LeanTheory.Chess.{krkBoard, krkPos, play_krk_king, play_krk_rook, play_krk_black, krkStateOK, krk_table_sound}` |
| Audit evidence | not audited |
| Last updated | 2026-11-24: oracle, validator, checker and data; chunk checks running |

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

## Next

Kernel check of the 64 chunks (5 in parallel, 3.5 GB cap each); then the bridge to well-formed
positions (`krk_forcesMate_wellFormed`, bound 16), then the Black-to-move split and the full-game
version as for KQK.
