/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.Chess.Rules
public import LeanTheory.Certificates.KernelFact

/-!
# Sanity: fidelity of the chess rules kernel

Fixtures checking `LeanTheory.Chess` (`Kernel/Chess/Rules`) against the FIDE Laws (`S-1`) and the
standard move-generation counts (`S-3`). Each concrete fact is an equation of closed Boolean or
natural-number terms, proved by `kernel_fact`, which leaves `Eq.refl` for the kernel to evaluate
(no `decide`). Squares are written `sq f r` with file `f = 0…7` for `a…h` and rank `r = 1…8`.

Risk covered by each group:

* **Global regression** (`S-3`): the number of legal move sequences of length 1, 2, 3 from the
  initial position is 20, 400, 8 902 (`perft_one`, `perft_two`, `perft_three`).
* **Checkmate** (FIDE 5.1.1): Fool's mate is legal move by move and ends in checkmate
  (`foolsMate_checkmate`); the initial position is not checkmate (`initial_not_checkmate`).
* **Stalemate** (FIDE 5.2.1): a standard queen stalemate (`stalemate_fixture`), and the same
  position with White to move is neither (`stalemate_needs_turn`).
* **Castling** (FIDE 3.8): legal when the conditions hold (`castle_legal`), illegal through an
  attacked square (`castle_through_check`), illegal after the king has moved and returned
  (`castle_after_king_moved`), and the rook arrives on `f1` (`castle_moves_rook`).
* **En passant** (FIDE 3.7.3): legal immediately after the double step and removing the captured
  pawn (`enPassant_legal`, `enPassant_removes_pawn`), illegal one move later
  (`enPassant_expires`).
* **Promotion** (FIDE 3.7.3.3): exactly four moves to the last-rank square (`promotion_four`).
* **Pins** (FIDE 3.9.2): a pinned bishop has pseudo-legal moves but no legal move
  (`pinned_bishop_pseudo`, `pinned_bishop_no_moves`): the legality filter excludes something.
-/

@[expose] public section

namespace LeanTheory.Sanity.Chess

open LeanTheory.Chess

/-! ### Global regression: perft -/

/-- 20 legal moves in the initial position. -/
theorem perft_one : perft 1 initialPosition = 20 := by kernel_fact

/-- 400 legal two-move sequences from the initial position. -/
theorem perft_two : perft 2 initialPosition = 400 := by kernel_fact

/-- 8 902 legal three-move sequences from the initial position. -/
theorem perft_three : perft 3 initialPosition = 8902 := by kernel_fact

/-! ### Checkmate and stalemate -/

/-- Fool's mate: 1. f3 e5 2. g4 Qh4#. -/
def foolsMate : List Move := [mv 5 2 5 3, mv 4 7 4 5, mv 6 2 6 4, mv 3 8 7 4]

/-- Every move of Fool's mate is legal and the final position is checkmate. -/
theorem foolsMate_checkmate :
    (playLegal initialPosition foolsMate).map isCheckmate = some true := by
  kernel_fact

/-- The initial position is neither checkmate nor stalemate. -/
theorem initial_not_checkmate :
    isCheckmate initialPosition = false ∧ isStalemate initialPosition = false := by
  kernel_fact

/-- Black: king a8; White: queen b6, king h1. -/
def stalematePieces : List (Square × Piece) :=
  [(sq 0 8, ⟨.black, .king⟩), (sq 1 6, ⟨.white, .queen⟩), (sq 7 1, ⟨.white, .king⟩)]

/-- With Black to move this is stalemate, not checkmate. -/
theorem stalemate_fixture :
    isStalemate (Position.ofList stalematePieces .black) = true ∧
      isCheckmate (Position.ofList stalematePieces .black) = false := by
  kernel_fact

/-- With White to move the same placement is neither stalemate nor checkmate. -/
theorem stalemate_needs_turn :
    isStalemate (Position.ofList stalematePieces .white) = false ∧
      isCheckmate (Position.ofList stalematePieces .white) = false := by
  kernel_fact

/-! ### Castling -/

/-- White: king e1, rook h1; Black: king a8 and optionally a rook; White to move with only the
white kingside castling right. -/
def castlePos (extra : List (Square × Piece)) : Position :=
  ⟨Board.ofList ([(sq 4 1, ⟨.white, .king⟩), (sq 7 1, ⟨.white, .rook⟩),
    (sq 0 8, ⟨.black, .king⟩)] ++ extra), .white, ⟨true, false, false, false⟩, none, 0⟩

/-- Castling kingside (`e1–g1`) is legal when the conditions of FIDE 3.8 hold. -/
theorem castle_legal : isLegal (castlePos []) (mv 4 1 6 1) = true := by kernel_fact

/-- After castling the rook stands on `f1` and `h1` is empty. -/
theorem castle_moves_rook :
    ((play (castlePos []) (mv 4 1 6 1)).board (sq 5 1) == some ⟨.white, .rook⟩) = true ∧
      ((play (castlePos []) (mv 4 1 6 1)).board (sq 7 1) == none) = true := by
  kernel_fact

/-- A black rook on `f8` attacks `f1`, the square the king crosses: castling is illegal. -/
theorem castle_through_check :
    isLegal (castlePos [(sq 5 8, ⟨.black, .rook⟩)]) (mv 4 1 6 1) = false := by
  kernel_fact

/-- After `Ke2 Kb8 Ke1 Ka8` the king is back on `e1` but castling is no longer legal. -/
theorem castle_after_king_moved :
    (playLegal (castlePos []) [mv 4 1 4 2, mv 0 8 1 8, mv 4 2 4 1, mv 1 8 0 8]).map
      (fun p => isLegal p (mv 4 1 6 1)) = some false := by
  kernel_fact

/-! ### En passant -/

/-- White: king h1, pawn e5; Black: king a8, pawn d7; Black to move. -/
def epPos : Position :=
  Position.ofList [(sq 7 1, ⟨.white, .king⟩), (sq 4 5, ⟨.white, .pawn⟩),
    (sq 0 8, ⟨.black, .king⟩), (sq 3 7, ⟨.black, .pawn⟩)] .black

/-- After `d7–d5`, the capture `e5×d6` en passant is legal. -/
theorem enPassant_legal :
    (playLegal epPos [mv 3 7 3 5]).map (fun p => isLegal p (mv 4 5 3 6)) = some true := by
  kernel_fact

/-- The en passant capture removes the black pawn from `d5`. -/
theorem enPassant_removes_pawn :
    (playLegal epPos [mv 3 7 3 5, mv 4 5 3 6]).map (fun p => p.board (sq 3 5) == none) =
      some true := by
  kernel_fact

/-- If White first plays `Kg1` and Black `Kb8`, the en passant capture is no longer legal. -/
theorem enPassant_expires :
    (playLegal epPos [mv 3 7 3 5, mv 7 1 6 1, mv 0 8 1 8]).map
      (fun p => isLegal p (mv 4 5 3 6)) = some false := by
  kernel_fact

/-! ### Promotion -/

/-- White: king h1, pawn b7; Black: king h8; White to move. -/
def promoPos : Position :=
  Position.ofList [(sq 7 1, ⟨.white, .king⟩), (sq 1 7, ⟨.white, .pawn⟩),
    (sq 7 8, ⟨.black, .king⟩)] .white

/-- The pawn on `b7` has exactly four legal moves, one for each promotion piece. -/
theorem promotion_four :
    ((legalMoves promoPos).filter fun m => m.src == sq 1 7).length = 4 ∧
      isLegal promoPos ⟨sq 1 7, sq 1 8, some .knight⟩ = true ∧
      isLegal promoPos (mv 1 7 1 8) = false := by
  kernel_fact

/-! ### Pins -/

/-- White: king e1, bishop e2; Black: rook e8, king a8; White to move. -/
def pinPos : Position :=
  Position.ofList [(sq 4 1, ⟨.white, .king⟩), (sq 4 2, ⟨.white, .bishop⟩),
    (sq 4 8, ⟨.black, .rook⟩), (sq 0 8, ⟨.black, .king⟩)] .white

/-- The pinned bishop has the pseudo-legal move `e2–d3`. -/
theorem pinned_bishop_pseudo : (pseudoMoves pinPos).contains (mv 4 2 3 3) = true := by
  kernel_fact

/-- The pinned bishop has no legal move: each would expose the king to the rook. -/
theorem pinned_bishop_no_moves :
    ((legalMoves pinPos).filter fun m => m.src == sq 4 2).length = 0 := by
  kernel_fact

end LeanTheory.Sanity.Chess
