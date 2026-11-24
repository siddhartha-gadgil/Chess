# Theory development and verification plan

This is the project index and plan of record. Replace every `‹…›` slot with domain content. Keep
stable identifiers when titles or priorities change; detailed work belongs in notes following
`notes/note-template.md`.

## 0. Current status

Repository `Chess`: a theory of chess, with the rules encoded from the FIDE Laws of Chess (2023).
Seeded 2026-11-20 with goals `G-1`–`G-4`, questions `Q-1`–`Q-9` and notes `N-01`–`N-09`
(`notes/chess/`). The library builds warning-free and passes the axiom audit (§4).

- Verified: **KQK is a forced win for White to move, within 10 moves** (`kqk_forcesMate_wellFormed`,
  `G-2`); chess is a determined finite game (`chess_determined_initial`, `G-3(a)`); KvK and KNvK
  are dead, and KBvK (`N-07`); in the full game with draw rules KQK from a fresh start is a win
  (`kqk_game_whiteWins_wellFormed`); game states, FIDE automatic draws, `wellFormed`, `ForcesMate` with a sound checker
  (`N-03`); the rules kernel `LeanTheory.Chess` with its fixtures (perft 20/400/8 902 and special
  moves; `N-02`), and abstract Zermelo determinacy `LeanTheory.Games` (`N-04`).
- Sourced: FIDE rules (`S-1`); Zermelo determinacy (`S-4`).
- Computational observations, not proofs here: KQK is a forced win, commonly cited maximum
  depth 10 (`S-6`); ≈ 4.8 × 10^44 legal positions (`S-5`).
- Open: the value of chess under perfect play (`Q-5`). This project can prove that a value exists
  (`N-04`) and certify small endgames; settling the value is not expected (`N-08`).
- Rule model decided: `Q-1` = A (FIDE automatic draws). Defaults adopted for `Q-2`, `Q-3`
  (proposals in `N-02`, `N-05`); revisit if they cause trouble.

## 1. Goal registry

Several goals may coexist. Goals may be independent or support other goals.

| ID | Goal and success criterion | Supports / supported by | Status | Evidence needed |
| --- | --- | --- | --- | --- |
| `G-1` | **Faithful rules kernel.** Computable Lean definitions of positions, legal moves (FIDE Arts 2–3) and outcomes (Arts 1, 5, 9.6), with a sanity suite: perft(1..3) from the start = 20 / 400 / 8 902, castling, en passant, promotion, pin, checkmate and stalemate fixtures, replay of recorded games | supports `G-2`, `G-3`, `G-4` | open | compiled `N-02`, `N-03`, `N-09` with sanity theorems; audit |
| `G-2` | **KQK is a win.** Compiled theorem: from every well-formed state with only WK, WQ, BK and White to move, White forces checkmate within `N` moves (target `N = 10`) against every defence; plus a precise Black-to-move case split | supported by `G-1`; supports `G-4` | **achieved** for White to move, also in the full game with draw rules (`kqk_forcesMate_wellFormed`, `kqk_game_whiteWins_wellFormed`); Black-to-move split open | `kqk_forcesMate`, `kqk_forcesMate_wellFormed` (`N-05`) |
| `G-3` | **Perfect play.** (a) Compiled determinacy: under the chosen rule model every state has a value in {White wins, draw, Black wins} with optimal strategies. (b) Determine the value of the initial position | supported by `G-1`, `G-4` | (a) **achieved** (`chess_determined_initial`), (b) open research problem, not expected to be achieved | (a) `N-04`; (b) no feasible route known (`N-08`) |
| `G-4` | **Further endgame theory.** Dead-position results (KvK, KBvK, KNvK) and further certified endgames (KRK, KBBK, KBNK, KPK) using the `G-2` method | supported by `G-1`, `G-2`; supports `G-3` | open | `N-07`; later notes |


## 2. Question registry

Questions may be primary research outputs or auxiliary prerequisites.

| ID | Question | Needed by | Status | Current best answer / barrier |
| --- | --- | --- | --- | --- |
| `Q-1` | Which rule model defines "perfect play": (A) FIDE automatic draws 9.6 only, (B) A plus claimable 9.2/9.3 draws, (C) idealised repetition-draw without move-count rule? | `G-3`, `N-03`, `N-04` | answered 2026-11-20 | **Model A (FIDE automatic: checkmate, stalemate, dead position, 9.6.1 fivefold, 9.6.2 75-move)**, chosen by the user |
| `Q-2` | What is a position in the kernel: placement, side to move, castling rights, en passant target, halfmove clock; how is repetition (9.2.3: same legal moves) represented? | `N-02`, `N-03` | answered (default adopted 2026-11-20) | Placement, side to move, castling rights, en passant target, halfmove clock; history outside the position |
| `Q-3` | Do theorems quantify over well-formed states or over FIDE-reachable positions (3.10.3)? | `G-2`, `G-4`, `N-05` | answered (default adopted 2026-11-20) | Well-formed states (stronger, avoids reachability) |
| `Q-4` | Exact KQK maximum depth to mate (White to move) and the Black-to-move case split | `G-2`, `N-05` | partly answered | Mate within 10 **proved** (`kqk_forcesMate`); that 10 is attained is an observation (`N-06`); Black-to-move split open |
| `Q-5` | Value of chess under perfect play | `G-3` | open research problem | Unknown; see `N-08` |
| `Q-5a` | Is the game determined under the chosen rule model? | `G-3`, `Q-5` | open (answer known in literature) | Yes, by Zermelo (`S-4`); to formalise in `N-04` |
| `Q-6` | How to define and decide dead positions (5.2.2) | `N-03`, `N-07` | open | Semantic definition; decide only for special material |
| `Q-7` | Which collection of Kasparov games (URL, locators, terms of use) serves as fixtures? | `N-09` | open (user input) | none |
| `Q-8` | KQK proof route: human strategy, kernel-checked retrograde certificate, or hybrid with symmetry? | `N-05` | open | Recommended: certificate + symmetry |
| `Q-9` | Which partial results toward `Q-5` are feasible and worthwhile? | `G-3` | open | Determinacy, certified endgames (`N-08`) |


## 3. Note registry and dependency graph

| ID | Note | Addresses | Depends on | Difficulty | Status / Lean readiness | Next action |
| --- | --- | --- | --- | --- | --- | --- |
| `N-01` | `chess/N-01-fide-rules-synthesis.md` — FIDE rules synthesis | `G-1`, `Q-1`–`Q-3`, `Q-6` | `S-1` | routine | stated / not Lean | Confirm decisions `Q-1`–`Q-3` |
| `N-02` | `chess/N-02-kernel-board-moves.md` — kernel: board, moves | `G-1`, `Q-2` | `N-01` (stated) | moderate | **verified** (fixtures; findings `A-1`–`A-3`) | Add missing special-move fixtures; well-formedness in `N-03` |
| `N-03` | `chess/N-03-outcomes-draw-rules.md` — outcomes, draw rules, `ForcesMate`, well-formedness | `G-1`, `G-3`, `Q-1`, `Q-6` | `N-02` (compiled ✓), `Q-1` (✓ model A) | moderate | **verified** | Chess `Game` instance (with `N-04`) |
| `N-04` | `chess/N-04-determinacy.md` — Zermelo determinacy | `G-3`, `Q-5a` | abstract: none; chess: `N-03` (compiled) | routine–moderate | **verified** (abstract + chess instance) | Done; `G-3(a)` achieved |
| `N-05` | `chess/N-05-kqk-strategy.md` — KQK forced mate | `G-2`, `Q-4`, `Q-8` | `N-02` ✓, `N-03` ✓ (compiled); `N-06` ✓ (data only) | moderate–hard | **verified** (White to move) | Black-to-move split; transfer to `GameState` |
| `N-06` | `chess/N-06-kqk-retrograde-oracle.md` — KQK oracle | `Q-4`, `Q-8` | `N-01` | routine | **complete** (observation): all WTM wins, max DTM 10 | Feed certificate to `N-05` |
| `N-07` | `chess/N-07-dead-positions.md` — dead positions | `G-1`, `G-4`, `Q-6` | `N-02` ✓, `N-03` ✓ | moderate | **verified** KvK, KNvK, KBvK | Optional: KB v KB same colour, blocked pawns |
| `N-08` | `chess/N-08-value-of-chess.md` — value of chess: status | `G-3`, `Q-5`, `Q-9` | `N-04` | research | exploratory / not Lean | Keep as guard against overclaiming |
| `N-09` | `chess/N-09-game-fixtures.md` — recorded games as fixtures | `G-1`, `Q-7` | `N-02` (compiled), `Q-7` | routine–moderate | stated / blocked | Choose source |

Dependency graph (→ = "is needed by"; nothing is established yet):

```text
S-1 → N-01 → N-02 → N-03 → N-05 → G-2 → G-4
                 │      ├→ N-07 → G-4
                 │      └→ N-04(chess) → G-3(a) ┄┄> G-3(b) [open, N-08]
                 └→ N-09 (needs Q-7)
N-04(abstract) → N-04(chess)          N-01 → N-06 ┄data┄> N-05
```

Ready now: `N-05` (KQK certificate), `N-07` (dead positions), `N-04` chess instance.

A dependency is established only when its required output is a compiled Lean declaration. A note
may explore a conditional dependency, but the edge and all downstream status must remain marked
unverified.

## 4. Strict audit status

The canonical first command is `start`. Record the audit before new theory builds on the checkout.

| Audit | Value |
| --- | --- |
| Audited commit | Working tree on `e001ebc` + KQK assembly (2026-11-24); previous: 2026-11-20 audits of `e644cf8` and the chess kernel |
| Scope | All chess code: `Kernel/Chess/{Rules,Game}`, `Sanity/Chess/*`, `Theory/Games/Determinacy`, `Theory/Chess/{Determinacy,DeadPositions}`, `Certificates/Chess/*`; template code unchanged |
| Kernel coverage | Complete for the `LeanTheory.Chess` kernel. Change since last audit: `Square.shift` reimplemented with natural-number bounds checks (same semantics); all three rules sanity suites re-run and pass |
| Commands run | `lake build` (memory-capped) — success, 3 320 jobs, zero warnings; `scripts/check_axioms.lean` — passed for 11 648 declarations; `#print axioms kqk_forcesMate_wellFormed` — standard three only; 64 KQK chunk modules built under 3.5 GB cgroup caps, all pass |
| Open findings | `A-3` (low, en passant trusts `epTarget`; mitigated by `wellFormed`). New `A-4` (low): KQK theorem assumes castling flags `none`. New `A-5` (resource): kernel checks of large certificates must be split into small declarations and run memory-capped (`systemd-run --user --scope -p MemoryMax=…`; `ulimit -v` breaks Lean) — a single 4096-entry declaration reached 11 GB |
| Missing sanity checks | Recorded-game replay (`N-09`); exactness of the KQK depth bound 10 not proved |

Previous code is in scope. A full startup audit inventories and red-teams every kernel declaration,
then traces findings into dependent results. After a kernel or foundational change, update the
audited commit only after rechecking affected code. Unresolved kernel findings block dependent
items from verified status.

## 5. Corrections and assumption ledger

Sources (`S-*`):

| ID | Source | Kind | Locator / validity |
| --- | --- | --- | --- |
| `S-1` | FIDE *Laws of Chess*, approved 2022-08-07, in force 2023-01-01 | Rule definition (normative) | https://handbook.fide.com/chapter/E012023, Arts 1–5, 9.2.3, 9.3, 9.6 (accessed 2026-11-20) |
| `S-2` | Kasparov's games "from the internet" (user) | Empirical game records | **No collection or locator given** (`Q-7`); valid only as rule-fidelity fixtures |
| `S-3` | Perft counts: initial position 20, 400, 8 902, 197 281; Kiwipete 48, 2 039, 97 862 | Computational, widely reproduced | https://www.chessprogramming.org/Perft_Results (fetched 2026-11-20) |
| `S-4` | E. Zermelo (1913), determinacy of chess-like games | Published theorem | Bibliographic details to be recorded |
| `S-5` | J. Tromp, number of legal chess positions ≈ 4.8 × 10^44; combined estimate (4.822 ± 0.028) × 10^44 | Numerical estimate (sampling) | https://tromp.github.io/chess/chess.html ; talkchess thread |
| `S-6` | Endgame tablebases (Wikipedia "Endgame tablebase"; chessprogramming.org "Endgame Tablebases"); KQK max DTM 10 commonly cited | Computational observation | KQK depth not confirmed from a primary source |

User ideas: `U-1` "trap kings against the edge" (box-shrinking KQK strategy, `N-05` route a);
`U-2` "guard against stalemates" (stalemate-avoidance lemma, `N-05`).

Model assumptions: the game is defined by `S-1` Arts 1–5 and the rule model of `Q-1` (pending;
proposed A). The rules are definitions, encoded as computable Lean functions, not as laws; their
fidelity to `S-1` is tested by sanity fixtures, never assumed.

Corrections:

- `C-1`: "Perfect play results in a draw" is a conjecture/belief, not a known result. Known:
  the value exists (Zermelo). Replace with `G-3(a)` determinacy plus open `G-3(b)`.
- `C-2`: "Insufficient material" is sufficient, not necessary, for a dead position (5.2.2).
- `C-3`: "KQ v K is a win" is false as stated for Black to move when Black can capture an
  undefended queen or is stalemated. Precise form in `G-2`/`N-05`.
- `C-5`: Repetition (9.2.3) is modelled as same side to move, placement, castling-right flags
  and legal-move set of the side to move (`samePosition`).
- `C-4`: Recorded master games, including Kasparov's, do not bear on the perfect-play value.

## 6. Theory tracks and model ladder

Tracks:

1. **Rules** (`N-01`, `N-02`, `N-03`, `N-09`): frontier empty. First deliverable: computable
   `legalMoves` with perft(1..3) sanity.
2. **Game theory** (`N-04`, `N-08`): frontier empty. First deliverable: abstract finite-game
   determinacy.
3. **Endgames** (`N-05`, `N-06`, `N-07`): frontier empty. First deliverable: KQK oracle data,
   then a kernel-checked KQK certificate.

Model ladder: (i) rules without draw-by-repetition/move-count (enough for short forced mates);
(ii) model A, FIDE automatic draws; (iii) model B with claims. A forced mate within `n` moves
proved at rung (i) from a fresh history transfers to (ii) and (iii) when `n` is below the
draw thresholds (to be proved as a lemma, not assumed).

## 7. Work selection

Interactive mode: after each work unit report status and ask the user to choose a ready note, a
goal/question or a topic for discussion. Record user ideas and sources in the affected notes
(`add notes`/`modify notes` for a discussion, `update notes from ...` for files or URLs); changes to
implemented notes become separate code patch notes.

Autonomous mode (`keep working`): choose the highest-value ready note, preferring work that
unblocks several dependants, closes a validity gap, tests a risky conjecture or produces a reusable
theorem. Continue across work units without waiting for a choice; stop for a genuine user decision,
missing authorization or absence of useful ready work.

Current priority order:

1. KQK Black-to-move case split, to finish `G-2` in full.
2. Dead-position sanity: the initial position is not dead; KB v KB same-coloured bishops dead.
3. Next certified endgame (KRK) reusing the KQK pipeline (`G-4`); needs faster kernel move
   generation or symmetry to keep checking time reasonable.
4. `N-09` recorded-game replay (needs a game source, `Q-7`).

## 8. Running a work unit

1. Resolve the selected `G-*`, `Q-*`, `N-*` or discussion topic to one coherent task.
2. Check dependency evidence and read the relevant notes, sources and compiled declarations.
3. Perform literature study, discovery, proof, counterexample search, computation, formalization or
   certification as appropriate to readiness.
4. Compile and strictly audit Lean output. For foundational changes, include existing affected
   code and add risk-specific or regression sanity checks. Do not promote an output to verified on
   informal evidence or on compilation alone.
5. Update the note graph, registries, barriers and this progress log.
6. Report verified and unverified outcomes separately and identify ready next work.

## 9. Definition of done

For a research note: claims and evidence are classified, dependencies and barriers are current,
outputs are recorded, and the next readiness-changing action is explicit.

For a verified result: declarations compile with docstrings and sanity theorems, zero warnings,
the axiom audit passes, semantic audit findings are resolved, entry points are registered, and the
note gives an honest scope statement. Kernel laws have the sanity triad plus risk-specific checks.

For a goal: all required contracts hold for compatible witnesses and models, and every claimed
dependency is backed by the recorded level of evidence. A formal theorem alone does not validate
the physical model.

## 10. Evidence gates

- `G-1`: compiled kernel + sanity theorems (perft, special-move fixtures, recorded-game replay);
  the fidelity evidence is the agreement with `S-1` and `S-3`, an external check.
- `G-2`: compiled `ForcesMate` theorem over the same kernel used by `G-1`'s sanity suite;
  any certificate data is untrusted until the checker soundness theorem compiles.
- `G-3(a)`: compiled determinacy for the same rule model as `Q-1`.

## 11. Progress log

- 2026-11-20 — `start`: full startup audit of template commit `e644cf8` (§4).
- 2026-11-20 — Seeding: created `G-1`–`G-4`, `Q-1`–`Q-9`, `N-01`–`N-09`, sources `S-1`–`S-6`,
  corrections `C-1`–`C-4`. FIDE rule text checked against `S-1`. No Lean written.
- 2026-11-20 — `Q-1` answered (model A, user). `Q-2`, `Q-3` defaults adopted. Work unit
  `N-02` + `N-04` (parallel, sub-agent for `N-04`): rules kernel `Kernel/Chess/Rules.lean` with
  17 sanity theorems (perft 1–3 by kernel evaluation, ≈ 3 min for the sanity file); abstract
  determinacy `Theory/Games/Determinacy.lean`. Audit findings `A-1`–`A-3`. Next ready: `N-03`,
  `N-06`.
- 2026-11-20 — `N-03` compiled (`Kernel/Chess/Game.lean`, 20 sanity theorems), resolving
  `A-1`/`A-2`. `N-06` (sub-agent): KQK all White-to-move wins, max DTM 10, validated
  independently (observation). `Q-4` answered at observation level. Work on branch
  `chess-theory`, committed and pushed per stage.
- 2026-11-24 — Work now committed directly to `main`. `N-04` chess instance (sub-agent):
  `chess_determined_initial`, finiteness via fivefold repetition. `N-07` (sub-agent): `dead_KK`,
  `dead_KNK`. `N-05`: KQK certificate checker with soundness, 64 chunk modules (4096 kernel
  checks) all pass; **`kqk_forcesMate_wellFormed` proved** (`G-2`, White to move). Memory
  incident: one kernel declaration grew to 11 GB; fixed by per-row declarations and cgroup caps
  (`A-5`).
- 2026-11-24 — `kqk_game_whiteWins_wellFormed` (KQK in `chessGame` with all model-A draw rules;
  rank argument, `KQKGame.lean`). `dead_KBK` (sub-agent, `DeadPositionsBishop.lean`). Build
  warning-free; axiom audit passed for 11 846 declarations.

## 12. Implementation and workstation log

Template build: 3 244 jobs, ≈ 1m23s. After chess work: 3 247 jobs. `Sanity/Chess/Rules.lean`
takes ≈ 3 min alone, dominated by `perft_three` (kernel evaluation of ≈ 9 000 leaves with a
function-valued board). Faster move generation will matter for KQK certificates (`N-05`).
Keep these distinct from mathematical evidence. See `workstation/REVIEWED.md`.
