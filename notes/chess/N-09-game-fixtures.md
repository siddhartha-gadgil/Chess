# N-09 — Recorded games as rule-fidelity fixtures

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-09` |
| Title | Replay real games (e.g. Kasparov's) through the kernel move generator |
| Kind | computation / sanity |
| Addresses | `G-1`, `Q-7` |
| Depends on | `N-02` |
| Dependency requirement | Compiled `legalMoves`, `play`; a SAN/PGN move parser |
| Produces | Regression theorems: each recorded move is legal in the kernel; final positions with result "checkmate" satisfy `IsCheckmate` |
| Difficulty | routine–moderate (SAN parsing, disambiguation) |
| Status | stated |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-20: created at seeding |

## Purpose and scope

The user named "Kasparov's games from the internet" as a source (`S-2`). Their sound use in this
project is as **empirical fixtures for rule fidelity**: if the kernel rejects a move from a real
game, the kernel (or the record) is wrong. They provide no evidence about perfect play.

Games that exercise castling on both sides, en passant, underpromotion and checkmate are the most
useful.

## Barriers

`S-2` has no specific collection, URL or licence yet (`Q-7`). Pick a stable source with
recorded locators (event, date, round) and check its terms of use before copying PGN into the
repository.

## Readiness

Blocked on `N-02` and on the choice of source.
