# N-04 — Determinacy of finite games (Zermelo) and its chess instance

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-04` |
| Title | Zermelo determinacy: abstract finite two-player games, then chess under rule model A |
| Kind | proof / formalization |
| Addresses | `G-3`, `Q-5`, `Q-5a` |
| Depends on | abstract part: none; chess part: `N-03` |
| Dependency requirement | Chess part needs `N-03` compiled under the chosen `Q-1` model and a proved bound on game length |
| Produces | `Theory/Games/Determinacy.lean` (planned): for every finite-depth game with outcomes in a linear order, the minimax value exists and each player has a strategy guaranteeing it; chess corollary: from every state exactly one of "White forces a win", "Black forces a win", "both force at least a draw" holds |
| Difficulty | abstract part routine–moderate (well-founded induction); chess length bound moderate |
| Status | abstract part verified; chess instance stated |
| Implementation status | abstract part complete; chess instance not started |
| Implementation evidence | `LeanTheory/Theory/Games/Determinacy.lean` |
| Lean evidence | `LeanTheory.Games.{Game, Game.value, Game.value_eq, Game.Strategy, Game.play, Game.optimal, Game.value_le_play_optimal, Game.play_optimal_le_value, Game.MaxForces, Game.MinForces, Game.maxForces_iff, Game.minForces_iff, Game.eq_value_of_forces, Game.GuaranteesGe, Game.GuaranteesLe, Game.guaranteesGe_iff, Game.guaranteesLe_iff, Outcome, Game.exactly_one_outcome, Game.maxForces_whiteWins_iff, Game.minForces_blackWins_iff}`; sanity `Game.sanity_terminal`, `subtractionGame_value`, `subtractionGame_three_four`, `no_bound_for_loop` |
| Audit evidence | 2026-11-20: statements reviewed; `MaxForces`/`MinForces` are defined through strategies and plays, not through `value`, so `maxForces_iff` has content |
| Last updated | 2026-11-20: abstract determinacy compiled (sub-agent, reviewed) |

## Purpose and scope

Make precise the only part of "what happens with perfect play" that is known: the game has a
value. This does **not** say what the value is (`Q-5`, open).

Abstract statement: a game is given by a type of states, a player-to-move function, a finite list
of successors and a terminal outcome; assume a well-founded "remaining length" (or a uniform depth
bound). Then `value` is defined by backward induction, and each player has a strategy
guaranteeing at least / at most `value`.

Chess instance (model A): the 75-move rule plus irreversibility of pawn moves and captures bound
every game. Sketch: each of the 16 pawns makes at most 6 forward moves (pawn moves ≤ 96), there are at most
30 captures, and between two consecutive such events there are fewer than 150 plies, so a game
has fewer than (96 + 30 + 1) × 150 plies. Fivefold repetition is not needed for finiteness.

## Sources and prior work

- `S-4`: E. Zermelo, "Über eine Anwendung der Mengenlehre auf die Theorie des Schachspiels"
  (1913). Published theorem; the modern backward-induction formulation differs from the
  original. Locator details to be added.
- Mathlib: search for existing game-tree / combinatorial game determinacy before building
  (`Mathlib/SetTheory/PGame` handles partizan games with a different convention, last player to
  move wins, and does not directly fit).

## Claims and evidence

- Compiled (abstract): for every `g : Game S α` (states, player to move, successor list, terminal
  outcome in a linear order, depth bound `bound` strictly decreasing along moves), `g.value s` is
  forced by both players and no better bound can be forced (`maxForces_iff`, `minForces_iff`);
  for `Outcome` (`blackWins < draw < whiteWins`) exactly one of the three cases holds
  (`exactly_one_outcome`). Strategies are positional over states; chess states will carry
  history, so this covers history-dependent play.
- For the chess instance: `moves` must be empty at automatic draws (75-move, fivefold) and
  checkmate/stalemate/dead positions, and `bound_lt` (the ply bound) must be proved.

- Ply bound for model A: proof sketch above; the counting of pawn moves needs care with
  promotions (a promoted pawn no longer makes pawn moves), which only helps.

## Difficulty, barriers and readiness

The abstract part is done. The chess instance is blocked on `N-03` (game states with history and
the draw rules), then needs the ply bound.

## Outputs and next dependencies

Provides the precise meaning of `G-3`: compute `value initialState`. The theorem leaves the value
itself open.
