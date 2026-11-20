# N-06 — KQK retrograde analysis (untrusted oracle)

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-06` |
| Title | Exploratory retrograde computation of KQK depth to mate |
| Kind | computation |
| Addresses | `Q-4`, `Q-8`, `G-2` |
| Depends on | `N-01` (rules for three pieces only) |
| Dependency requirement | Rule fidelity for K, Q moves and check only; no Lean dependency |
| Produces | Python script under `notes/reasoning/<date>-kqk-oracle/computations/`; table of states, depth-to-mate distribution, maximum depth, count of stalemates and of states where Black captures the queen; a candidate certificate format for `N-05` |
| Difficulty | routine |
| Status | complete (numerical observation, untrusted) |
| Implementation status | complete |
| Implementation evidence | `notes/reasoning/2026-11-20-kqk-oracle/` (oracle, independent validator, candidate certificate) |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-20: computed (sub-agent), validated by an independent script |

## Purpose and scope

Quantify what `N-05` must certify: number of well-formed states after symmetry reduction, depth
distribution, maximum depth (to confirm or correct the commonly cited 10). Results are numerical
observations: they do not count as evidence for `G-2` until checked in Lean.

## Results (numerical observations, not proofs)

- Well-formed KQK states: 144 508 White to move (18 081 up to the 8 board symmetries), 223 944
  Black to move (28 056 up to symmetry).
- **Every White-to-move state is a forced mate; maximum depth 10**, reached only from WK a1, WQ
  b2, BK f5 and its symmetric copies. Depth distribution 1…10: 2448, 5012, 9064, 19964, 26164,
  32064, 32104, 15000, 2680, 8. Agrees with Wikipedia "Checkmate" (mate in at most ten moves).
- Black to move: 200 532 White mates (max 10), 22 176 Black captures the undefended queen (draw),
  872 stalemates, 364 already checkmated.
- A mate needs at most 19 plies (White to move), far below the 150 of the 75-move rule; along a
  depth-decreasing line no position repeats.
- Independent validator: 0 errors (move legality, exact depths, symmetry invariance).
- Candidate certificate: `computations/kqk_wtm_canonical_cert.tsv` (18 081 rows: canonical
  state, depth, move). Proposal and cost estimate in the task README.

## Difficulty, barriers and readiness

Ready now. Uses `scripts/setup.sh --python --no-build` and `.venv-ws`. Cross-check the output
against an independent source (published KQK statistics) and record any disagreement.

## Outputs and next dependencies

Answers `Q-4` at the level of a numerical observation; fixes the certificate size for `N-05`.
