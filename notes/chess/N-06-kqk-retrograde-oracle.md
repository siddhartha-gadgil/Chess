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
| Status | exploratory |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-20: created at seeding |

## Purpose and scope

Quantify what `N-05` must certify: number of well-formed states after symmetry reduction, depth
distribution, maximum depth (to confirm or correct the commonly cited 10). Results are numerical
observations: they do not count as evidence for `G-2` until checked in Lean.

## Difficulty, barriers and readiness

Ready now. Uses `scripts/setup.sh --python --no-build` and `.venv-ws`. Cross-check the output
against an independent source (published KQK statistics) and record any disagreement.

## Outputs and next dependencies

Answers `Q-4` at the level of a numerical observation; fixes the certificate size for `N-05`.
