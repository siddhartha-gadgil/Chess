/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.Chess.Game
public import LeanTheory.Certificates.KernelFact

/-!
# Sanity: well-formedness, repetition, automatic draws and forced mates

Fixtures for `Kernel/Chess/Game` (note `N-03`). Concrete facts are proved by `kernel_fact`
(kernel evaluation, no `decide`); forced mates go through the checker soundness theorem
`forcesMateB_sound`. Risk covered:

* **Well-formedness** (`A-1`): the initial position is well formed; a missing king, the side not
  to move in check, a pawn on the last rank and a stray en passant target are each rejected.
* **Repetition** (FIDE 9.2.3, `A-2`): knights out and back reproduce the initial position; the
  en passant field is ignored when no en passant capture is possible
  (`samePosition_ignores_dead_ep`) but counts when one is (`samePosition_live_ep`).
* **Fivefold repetition** (9.6.1): four repetitions do not end the game, five do.
* **75-move rule** (9.6.2): 150 plies without capture or pawn move draw, but checkmate takes
  precedence.
* **Forced mates**: a mate in one is found and certified (`mateInOne`), it is not a mate in zero
  (degenerate case `ForcesMate.not_zero`), the same position is not dead
  (`mateInOne_not_dead`), and a natural-looking queen move stalemates instead (`stalemateTrap`),
  the hazard of user idea `U-2`. A position with no mate in one is rejected by the checker
  (`noMateInOne`).
-/

@[expose] public section

namespace LeanTheory.Sanity.Chess

open LeanTheory.Chess

/-! ### Well-formedness -/

/-- The initial position is well formed. -/
theorem wellFormed_initial : wellFormed initialPosition = true := by kernel_fact

/-- A position without a black king is not well formed. -/
theorem not_wellFormed_noKing :
    wellFormed (Position.ofList [(sq 4 1, ⟨.white, .king⟩)] .white) = false := by kernel_fact

/-- White to move while the black king is in check (from the queen on `e2`) is not well
formed. -/
theorem not_wellFormed_check :
    wellFormed (Position.ofList [(sq 0 1, ⟨.white, .king⟩), (sq 4 2, ⟨.white, .queen⟩),
      (sq 4 8, ⟨.black, .king⟩)] .white) = false := by kernel_fact

/-- A white pawn on the eighth rank is not well formed. -/
theorem not_wellFormed_pawn :
    wellFormed (Position.ofList [(sq 0 1, ⟨.white, .king⟩), (sq 3 8, ⟨.white, .pawn⟩),
      (sq 7 8, ⟨.black, .king⟩)] .white) = false := by kernel_fact

/-- The initial position with an en passant target on `e3` is not well formed (no pawn has just
made a double step). -/
theorem not_wellFormed_ep :
    wellFormed { initialPosition with epTarget := some (sq 4 3) } = false := by kernel_fact

/-- After `1. e4` the position (with en passant target `e3`) is well formed. -/
theorem wellFormed_after_e4 :
    (playLegal initialPosition [mv 4 2 4 4]).map wellFormed = some true := by kernel_fact

/-! ### Repetition -/

/-- `1. Nf3 Nf6 2. Ng1 Ng8` returns to the initial position. -/
def knightDance : List Move := [mv 6 1 5 3, mv 6 8 5 6, mv 5 3 6 1, mv 5 6 6 8]

/-- The position after the knight dance is the same as the initial position (9.2.3). -/
theorem knightDance_same :
    (playLegal initialPosition knightDance).map (samePosition initialPosition) = some true := by
  kernel_fact

/-- After `1. e4` the en passant target `e3` is set, but Black has no en passant capture, so the
position is the same as the one without the target. -/
theorem samePosition_ignores_dead_ep :
    (playLegal initialPosition [mv 4 2 4 4]).map
      (fun p => samePosition p { p with epTarget := none }) = some true := by
  kernel_fact

/-- White: king h1, pawn e5; Black: king a8, pawn d7; Black to move. -/
def epPos' : Position :=
  Position.ofList [(sq 7 1, ⟨.white, .king⟩), (sq 4 5, ⟨.white, .pawn⟩),
    (sq 0 8, ⟨.black, .king⟩), (sq 3 7, ⟨.black, .pawn⟩)] .black

/-- After `d7–d5` White can capture en passant, so the position differs from the one without the
en passant target. -/
theorem samePosition_live_ep :
    (playLegal epPos' [mv 3 7 3 5]).map
      (fun p => samePosition p { p with epTarget := none }) = some false := by
  kernel_fact

/-! ### Fivefold repetition and the 75-move rule -/

/-- After the knight dance three times the initial position has appeared four times: no draw. -/
theorem fourfold_not_draw :
    (GameState.playLegal (.start initialPosition) (knightDance ++ knightDance ++ knightDance)).map
      (fun g => (g.repetitions, g.automaticDraw)) = some (4, false) := by
  kernel_fact

/-- After the knight dance four times the initial position has appeared five times: automatic
draw (9.6.1). -/
theorem fivefold_draw :
    (GameState.playLegal (.start initialPosition)
      (knightDance ++ knightDance ++ knightDance ++ knightDance)).map
      (fun g => (g.repetitions, g.automaticDraw)) = some (5, true) := by
  kernel_fact

/-- Black: king h8; White: king g6, queen a7. -/
def mateInOnePieces : List (Square × Piece) :=
  [(sq 7 8, ⟨.black, .king⟩), (sq 6 6, ⟨.white, .king⟩), (sq 0 7, ⟨.white, .queen⟩)]

/-- A quiet position with halfmove clock 150 is an automatic draw (9.6.2). -/
theorem seventyFive_draw :
    (GameState.start { Position.ofList mateInOnePieces .white with halfmove := 150 }).automaticDraw
      = true := by
  kernel_fact

/-- With clock 149 it is not. -/
theorem seventyFive_boundary :
    (GameState.start { Position.ofList mateInOnePieces .white with halfmove := 149 }).automaticDraw
      = false := by
  kernel_fact

/-- Checkmate on the 150th ply takes precedence over the 75-move rule: `Qa7–g7#` with the clock
reaching 150 is not a draw, and it is checkmate. -/
theorem seventyFive_mate_precedence :
    ((GameState.start { Position.ofList mateInOnePieces .white with halfmove := 149 }).play
        (mv 0 7 6 7)).automaticDraw = false ∧
      isCheckmate (play { Position.ofList mateInOnePieces .white with halfmove := 149 }
        (mv 0 7 6 7)) = true ∧
      (play { Position.ofList mateInOnePieces .white with halfmove := 149 }
        (mv 0 7 6 7)).halfmove = 150 := by
  kernel_fact

/-! ### Forced mates -/

/-- The mate-in-one position, White to move. -/
def mateInOnePos : Position := Position.ofList mateInOnePieces .white

/-- The checker finds a mate in one. -/
theorem mateInOne_check : forcesMateB .white 1 mateInOnePos = true := by kernel_fact

/-- **White forces mate within one move** (via the checker soundness theorem). -/
theorem mateInOne : ForcesMate .white 1 mateInOnePos :=
  forcesMateB_sound _ _ _ mateInOne_check

/-- Degenerate case: White, to move, has no mate within zero moves. -/
theorem mateInOne_not_zero : ¬ ForcesMate .white 0 mateInOnePos :=
  ForcesMate.not_zero rfl

/-- The mate-in-one position is not dead. -/
theorem mateInOne_not_dead : ¬ IsDead mateInOnePos := mateInOne.not_isDead

/-- The stalemate trap: `Qa7–f7` takes every square from the black king without giving check. -/
theorem stalemateTrap :
    isLegal mateInOnePos (mv 0 7 5 7) = true ∧
      isStalemate (play mateInOnePos (mv 0 7 5 7)) = true := by
  kernel_fact

/-- Black: king h8; White: king f5, queen b1; White to move. -/
def noMatePos : Position :=
  Position.ofList [(sq 7 8, ⟨.black, .king⟩), (sq 5 5, ⟨.white, .king⟩),
    (sq 1 1, ⟨.white, .queen⟩)] .white

/-- Counterexample for the checker: there is no mate in one here. -/
theorem noMateInOne : forcesMateB .white 1 noMatePos = false := by kernel_fact

end LeanTheory.Sanity.Chess
