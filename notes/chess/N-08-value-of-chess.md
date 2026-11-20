# N-08 — The value of chess under perfect play: status and barriers

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-08` |
| Title | Is chess a draw? Known facts, evidence levels and feasible sub-results |
| Kind | source synthesis / research approach |
| Addresses | `G-3`, `Q-5`, `Q-9` |
| Depends on | `N-04` (determinacy), `N-03` (rule model) |
| Dependency requirement | A compiled determinacy theorem is needed before "the value" can be referred to in Lean |
| Produces | An honest status statement; a list of feasible partial results (`Q-9`) |
| Difficulty | research (open problem; well beyond present computation) |
| Status | exploratory |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-20: created at seeding |

## Purpose and scope

Record what is and is not known, so that no project output overstates it.

| Claim | Evidence level |
| --- | --- |
| Chess (with a draw rule making it finite) has a value: White wins, Black wins or draw | Published theorem (`S-4`); planned compiled theorem `N-04` |
| The value is not known | Status of the field as far as is known on 2026-11-20 |
| About 4.8 × 10^44 legal (reachable) positions | Numerical estimate (`S-5`, Tromp; sampling estimate (4.822 ± 0.028) × 10^44) |
| All positions with at most 7 pieces are solved by tablebases | Computational result (`S-6`); not a proof in this project |
| Most strong players and engines believe the value is a draw | Heuristic opinion / empirical observation; not evidence of the value |
| Kasparov's games (`S-2`) | Empirical records of human play; no bearing on the value under perfect play |

## Barriers

1. State space size (≈ 10^44): full retrograde analysis or proof-number search is far beyond
   current resources, and a Lean-checkable certificate would be larger still.
2. No known structural argument: strategy stealing does not apply because zugzwang positions
   exist (a move can be a disadvantage), so "White cannot lose" is also open.
3. The value may depend on the rule model (`Q-1`).

## Feasible sub-results (`Q-9`)

- Determinacy (`N-04`).
- Values of small endgames (`G-2`, `G-4`), building toward certified tablebase fragments.
- Values of chess on small boards or restricted variants, as a methodology testbed (needs a user
  decision; it is a change of game, not a result about chess).

## Readiness

No Lean work is ready here; the note is a guard against overclaiming.
