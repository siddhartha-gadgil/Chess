# Log — 2026-11-20-kqk-oracle (N-06)

All results are numerical observations from untrusted Python; none is a proof.

- 2026-11-20. Read `notes/chess/N-06-kqk-retrograde-oracle.md`, `notes/chess/N-05-kqk-strategy.md`,
  square convention of `LeanTheory/Kernel/Chess/Rules.lean` (`Square = Fin 64`, `8*rank+file`).
- Created `.venv-ws` with `scripts/setup.sh --python --no-build` (Python 3.12.3). Standard
  library only.
- Wrote `computations/kqk_retro.py` (precomputed rays, iterative retrograde: pass `n` marks
  White-to-move states with a move to a Black-to-move state of value `<= n-1`; a Black-to-move
  state gets `max` over its replies once all are resolved; capture of an undefended queen marks
  the state `C` = draw). Run: `.venv-ws/bin/python kqk_retro.py` (14 s). Output
  `run_kqk_retro.out`, `kqk_summary.json`, `kqk_wtm.tsv`, `kqk_btm.tsv`,
  `kqk_wtm_canonical_cert.tsv`.
- Wrote `computations/kqk_validate.py`, an independent re-implementation (0x88 mailbox, generic
  "make move, is own king attacked by any enemy piece" legality, generic well-formedness). It
  re-derives the state sets and checks the defining equations of every table entry. Run (15 s):
  0 errors (`run_kqk_validate.out`).
- Wrote `computations/cert_size.py`: certificate sizes and a principal variation from the
  unique (up to symmetry) DTM-10 state (`run_cert_size.out`).
- Source check: Wikipedia "Checkmate", section King and queen (fetched 2026-11-20): "checkmate
  can be forced in at most ten moves from any starting position" (its notes 23, 24), and at most
  nine after a pawn has just promoted. Agrees with max DTM 10. chessprogramming.org KQK page
  and a Wikipedia KQK page were not found (404). Other figures are recalled only.
- Wrote `README.md`.
