/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.Chess.Rules
public import LeanTheory.Certificates.KernelFact

/-!
# Sanity: special moves and king safety in the chess rules kernel

Further fixtures for `LeanTheory.Chess` (`Kernel/Chess/Rules`), complementing
`LeanTheory.Sanity.Chess.Rules`, aimed at the classic move-generator bugs around the special
moves of the FIDE Laws (`S-1`). Each concrete fact is an equation of closed Boolean or
natural-number terms, proved by `kernel_fact`, which leaves `Eq.refl` for the kernel (no
`decide`). Squares are written `sq f r` with file `f = 0…7` for `a…h` and rank `r = 1…8`.

Risk covered by each group:

* **Queenside castling** (FIDE 3.8.2): `e1–c1` is legal when the conditions hold
  (`castleQ_legal`) and puts the rook on `d1` (`castleQ_moves_rook`); it is illegal when `b1` is
  occupied (`castleQ_b1_occupied`) but legal when `b1` is attacked and empty, since only the
  king's squares must be safe (`castleQ_b1_attacked`, a classic bug); it is illegal when `d1`,
  the square the king crosses, is attacked (`castleQ_d1_attacked`).
* **Black castling** (FIDE 3.8.2): `e8–g8` and `e8–c8` are legal and move the rooks to `f8` and
  `d8` (`castleBlack_legal`, `castleBlack_rooks`); a king in check cannot castle
  (`castleBlack_in_check`).
* **Castling right lost by capture** (FIDE 3.8.2.1 as encoded in FEN practice: a captured rook
  has "moved"): after `…Bxh1 Rxh1` a white rook stands on `h1` again, but castling is illegal
  (`castle_after_rook_captured`, with control `castle_without_capture`), and `play` clears the
  right (`capture_clears_right`).
* **Promotion** (FIDE 3.7.3.3): a black pawn on `b2` has four promotion moves
  (`blackPromotion_four`) and the promoted piece is on the board (`blackPromotion_piece`);
  promotion by capture gives four moves per capture square (`capturePromotion_counts`) and the
  promoted piece replaces the captured one (`capturePromotion_piece`).
* **Black en passant** (FIDE 3.7.3.1): after `e2–e4`, `d4×e3` is legal and removes the white pawn
  (`blackEnPassant`).
* **Double check** (FIDE 3.9): after a discovered double check only king moves are legal
  (`doubleCheck_only_king`), although captures of either checker are pseudo-legal
  (`doubleCheck_captures_pseudo`).
* **King safety** (FIDE 3.8.1, 3.9): a king may not move next to the opposing king
  (`kings_not_adjacent`) and may not capture a defended piece (`king_no_defended_capture`), but
  may capture it undefended (`king_undefended_capture`).
* **Global regression** (`S-3`, Kiwipete): perft 1 and 2 from a position rich in castling, en
  passant possibilities, promotions and pins are 48 and 2 039 (`kiwipete_perft_one`,
  `kiwipete_perft_two`).
-/

@[expose] public section

namespace LeanTheory.Sanity.Chess.SpecialMoves

open LeanTheory.Chess

/-- A position from a piece list, side to move and castling rights; no en passant target. -/
def posWith (l : List (Square × Piece)) (turn : Color) (cr : CastlingRights) : Position :=
  ⟨Board.ofList l, turn, cr, none, 0⟩

/-! ### Queenside castling (White) -/

/-- White: king e1, rook a1; Black: king h8 and `extra`; White to move, white queenside right
only. -/
def castleQPos (extra : List (Square × Piece)) : Position :=
  posWith ([(sq 4 1, ⟨.white, .king⟩), (sq 0 1, ⟨.white, .rook⟩),
    (sq 7 8, ⟨.black, .king⟩)] ++ extra) .white ⟨false, true, false, false⟩

/-- FIDE 3.8.2: queenside castling `e1–c1` is legal when all conditions hold. -/
theorem castleQ_legal : isLegal (castleQPos []) (mv 4 1 2 1) = true := by kernel_fact

/-- FIDE 3.8.2: after `e1–c1` the king is on `c1`, the rook on `d1`, and `a1`, `e1` are empty. -/
theorem castleQ_moves_rook :
    ((play (castleQPos []) (mv 4 1 2 1)).board (sq 2 1) == some ⟨.white, .king⟩) = true ∧
      ((play (castleQPos []) (mv 4 1 2 1)).board (sq 3 1) == some ⟨.white, .rook⟩) = true ∧
      ((play (castleQPos []) (mv 4 1 2 1)).board (sq 0 1) == none) = true ∧
      ((play (castleQPos []) (mv 4 1 2 1)).board (sq 4 1) == none) = true := by
  kernel_fact

/-- FIDE 3.8.2.2: a white knight on `b1` (between king and rook) makes castling illegal. -/
theorem castleQ_b1_occupied :
    isLegal (castleQPos [(sq 1 1, ⟨.white, .knight⟩)]) (mv 4 1 2 1) = false := by
  kernel_fact

/-- FIDE 3.8.2.2: a black rook on `b8` attacks the empty square `b1`, which the king does not
cross: castling is still legal (classic bug: requiring `b1` to be unattacked). -/
theorem castleQ_b1_attacked :
    attackedBy (castleQPos [(sq 1 8, ⟨.black, .rook⟩)]).board .black (sq 1 1) = true ∧
      isLegal (castleQPos [(sq 1 8, ⟨.black, .rook⟩)]) (mv 4 1 2 1) = true := by
  kernel_fact

/-- FIDE 3.8.2.2: a black rook on `d8` attacks `d1`, which the king crosses: castling is
illegal. -/
theorem castleQ_d1_attacked :
    isLegal (castleQPos [(sq 3 8, ⟨.black, .rook⟩)]) (mv 4 1 2 1) = false := by
  kernel_fact

/-! ### Castling for Black -/

/-- Black: king e8, rooks a8, h8; White: king h1 and `extra`; Black to move with both black
castling rights. -/
def castleBPos (extra : List (Square × Piece)) : Position :=
  posWith ([(sq 4 8, ⟨.black, .king⟩), (sq 0 8, ⟨.black, .rook⟩), (sq 7 8, ⟨.black, .rook⟩),
    (sq 7 1, ⟨.white, .king⟩)] ++ extra) .black ⟨false, false, true, true⟩

/-- FIDE 3.8.2: Black may castle on both sides, `e8–g8` and `e8–c8`. -/
theorem castleBlack_legal :
    isLegal (castleBPos []) (mv 4 8 6 8) = true ∧
      isLegal (castleBPos []) (mv 4 8 2 8) = true := by
  kernel_fact

/-- FIDE 3.8.2: after `e8–g8` the rook is on `f8`; after `e8–c8` it is on `d8`. -/
theorem castleBlack_rooks :
    ((play (castleBPos []) (mv 4 8 6 8)).board (sq 5 8) == some ⟨.black, .rook⟩) = true ∧
      ((play (castleBPos []) (mv 4 8 6 8)).board (sq 7 8) == none) = true ∧
      ((play (castleBPos []) (mv 4 8 2 8)).board (sq 3 8) == some ⟨.black, .rook⟩) = true ∧
      ((play (castleBPos []) (mv 4 8 2 8)).board (sq 0 8) == none) = true := by
  kernel_fact

/-- FIDE 3.8.2.2: with a white rook on `e2` the black king is in check and cannot castle on
either side. -/
theorem castleBlack_in_check :
    inCheck (castleBPos [(sq 4 2, ⟨.white, .rook⟩)]).board .black = true ∧
      isLegal (castleBPos [(sq 4 2, ⟨.white, .rook⟩)]) (mv 4 8 6 8) = false ∧
      isLegal (castleBPos [(sq 4 2, ⟨.white, .rook⟩)]) (mv 4 8 2 8) = false := by
  kernel_fact

/-! ### Castling right lost when the rook is captured -/

/-- White: king e1, rooks h1, h2; Black: king a7, bishop b7; Black to move, white kingside
right only. -/
def rookCapturePos : Position :=
  posWith [(sq 4 1, ⟨.white, .king⟩), (sq 7 1, ⟨.white, .rook⟩), (sq 7 2, ⟨.white, .rook⟩),
    (sq 0 7, ⟨.black, .king⟩), (sq 1 7, ⟨.black, .bishop⟩)] .black ⟨true, false, false, false⟩

/-- Control: after the quiet moves `…Ka6 Rh3 Ka7` (white kingside right untouched) castling
`e1–g1` is legal. -/
theorem castle_without_capture :
    (playLegal rookCapturePos [mv 0 7 0 6, mv 7 2 7 3, mv 0 6 0 7]).map
      (fun p => isLegal p (mv 4 1 6 1)) = some true := by
  kernel_fact

/-- FIDE 3.8.2.1: the capture `…Bxh1` removes the white kingside right in `play`. -/
theorem capture_clears_right :
    (play rookCapturePos (mv 1 7 7 1)).castling.whiteKing = false := by
  kernel_fact

/-- FIDE 3.8.2.1: after `…Bxh1 Rxh1 …Ka6` a white rook is back on `h1` and `f1`, `g1` are empty
and safe, but castling `e1–g1` is illegal because the right was lost. -/
theorem castle_after_rook_captured :
    (playLegal rookCapturePos [mv 1 7 7 1, mv 7 2 7 1, mv 0 7 0 6]).map
      (fun p => (p.board (sq 7 1) == some ⟨.white, .rook⟩) && !isLegal p (mv 4 1 6 1)) =
      some true := by
  kernel_fact

/-! ### Promotion -/

/-- Black: king h8, pawn b2; White: king h1; Black to move. -/
def blackPromoPos : Position :=
  Position.ofList [(sq 7 8, ⟨.black, .king⟩), (sq 1 2, ⟨.black, .pawn⟩),
    (sq 7 1, ⟨.white, .king⟩)] .black

/-- FIDE 3.7.3.3: the black pawn on `b2` has exactly four legal moves, all to `b1` with a
promotion piece; the move without promotion is illegal. -/
theorem blackPromotion_four :
    ((legalMoves blackPromoPos).filter fun m => m.src == sq 1 2).length = 4 ∧
      ((legalMoves blackPromoPos).filter fun m =>
        m.src == sq 1 2 && m.dst == sq 1 1 && m.promo.isSome).length = 4 ∧
      isLegal blackPromoPos (mv 1 2 1 1) = false := by
  kernel_fact

/-- FIDE 3.7.3.3: after `b2–b1=Q` a black queen stands on `b1` and `b2` is empty. -/
theorem blackPromotion_piece :
    ((play blackPromoPos ⟨sq 1 2, sq 1 1, some .queen⟩).board (sq 1 1) ==
        some ⟨.black, .queen⟩) = true ∧
      ((play blackPromoPos ⟨sq 1 2, sq 1 1, some .queen⟩).board (sq 1 2) == none) = true := by
  kernel_fact

/-- White: king h1, pawn b7; Black: king h8, rooks a8, c8; White to move. -/
def capturePromoPos : Position :=
  Position.ofList [(sq 7 1, ⟨.white, .king⟩), (sq 1 7, ⟨.white, .pawn⟩),
    (sq 7 8, ⟨.black, .king⟩), (sq 0 8, ⟨.black, .rook⟩), (sq 2 8, ⟨.black, .rook⟩)] .white

/-- FIDE 3.7.3.3: the pawn on `b7` has twelve legal moves: four promotions on each of `a8`
(capture), `b8` (advance) and `c8` (capture). -/
theorem capturePromotion_counts :
    ((legalMoves capturePromoPos).filter fun m => m.src == sq 1 7).length = 12 ∧
      ((legalMoves capturePromoPos).filter fun m =>
        m.src == sq 1 7 && m.dst == sq 0 8).length = 4 ∧
      ((legalMoves capturePromoPos).filter fun m =>
        m.src == sq 1 7 && m.dst == sq 2 8).length = 4 ∧
      isLegal capturePromoPos (mv 1 7 0 8) = false := by
  kernel_fact

/-- FIDE 3.7.3.3: after `b7×a8=N` a white knight replaces the black rook on `a8`. -/
theorem capturePromotion_piece :
    ((play capturePromoPos ⟨sq 1 7, sq 0 8, some .knight⟩).board (sq 0 8) ==
        some ⟨.white, .knight⟩) = true := by
  kernel_fact

/-! ### En passant by Black -/

/-- White: king h1, pawn e2; Black: king a8, pawn d4; White to move. -/
def blackEpPos : Position :=
  Position.ofList [(sq 7 1, ⟨.white, .king⟩), (sq 4 2, ⟨.white, .pawn⟩),
    (sq 0 8, ⟨.black, .king⟩), (sq 3 4, ⟨.black, .pawn⟩)] .white

/-- FIDE 3.7.3.1: after `e2–e4`, `…d4×e3` en passant is legal; it puts the black pawn on `e3`
and removes the white pawn from `e4`. -/
theorem blackEnPassant :
    (playLegal blackEpPos [mv 4 2 4 4, mv 3 4 4 3]).map
      (fun p => (p.board (sq 4 3) == some ⟨.black, .pawn⟩) && (p.board (sq 4 4) == none) &&
        (p.board (sq 3 4) == none)) = some true := by
  kernel_fact

/-! ### Discovered double check -/

/-- White: king h2, rook e1, knight e4; Black: king e8, queen a6, rook a1; White to move. -/
def doubleCheckPos : Position :=
  Position.ofList [(sq 7 2, ⟨.white, .king⟩), (sq 4 1, ⟨.white, .rook⟩),
    (sq 4 4, ⟨.white, .knight⟩), (sq 4 8, ⟨.black, .king⟩), (sq 0 6, ⟨.black, .queen⟩),
    (sq 0 1, ⟨.black, .rook⟩)] .white

/-- The position after the discovered double check `Ne4–f6+` (rook on `e1` and knight on `f6`
both give check). -/
def doubleCheckAfter : Position := play doubleCheckPos (mv 4 4 5 6)

/-- FIDE 3.9: in double check only king moves are legal; here exactly `Kd8`, `Kf8`, `Kf7`. -/
theorem doubleCheck_only_king :
    isLegal doubleCheckPos (mv 4 4 5 6) = true ∧
      inCheck doubleCheckAfter.board .black = true ∧
      (legalMoves doubleCheckAfter).length = 3 ∧
      (legalMoves doubleCheckAfter).all (fun m => m.src == sq 4 8) = true := by
  kernel_fact

/-- Capturing either checker (`…Qxf6`, `…Rxe1`) is pseudo-legal but not legal. -/
theorem doubleCheck_captures_pseudo :
    (pseudoMoves doubleCheckAfter).contains (mv 0 6 5 6) = true ∧
      (pseudoMoves doubleCheckAfter).contains (mv 0 1 4 1) = true ∧
      isLegal doubleCheckAfter (mv 0 6 5 6) = false ∧
      isLegal doubleCheckAfter (mv 0 1 4 1) = false := by
  kernel_fact

/-! ### King safety -/

/-- White: king e4; Black: king e6; White to move. -/
def kingsPos : Position :=
  Position.ofList [(sq 4 4, ⟨.white, .king⟩), (sq 4 6, ⟨.black, .king⟩)] .white

/-- FIDE 3.8.1, 3.9: the white king may not step to `d5`, `e5`, `f5` next to the black king,
though these moves are pseudo-legal; it has exactly five legal moves. -/
theorem kings_not_adjacent :
    (pseudoMoves kingsPos).contains (mv 4 4 4 5) = true ∧
      isLegal kingsPos (mv 4 4 3 5) = false ∧ isLegal kingsPos (mv 4 4 4 5) = false ∧
      isLegal kingsPos (mv 4 4 5 5) = false ∧ (legalMoves kingsPos).length = 5 := by
  kernel_fact

/-- White: king e1; Black: king a8, pawn e2 and `extra`; White to move. -/
def defendedPos (extra : List (Square × Piece)) : Position :=
  Position.ofList ([(sq 4 1, ⟨.white, .king⟩), (sq 0 8, ⟨.black, .king⟩),
    (sq 4 2, ⟨.black, .pawn⟩)] ++ extra) .white

/-- FIDE 3.9: the pawn on `e2` defended by a knight on `c3` cannot be captured by the king. -/
theorem king_no_defended_capture :
    isLegal (defendedPos [(sq 2 3, ⟨.black, .knight⟩)]) (mv 4 1 4 2) = false := by
  kernel_fact

/-- Control: the undefended pawn on `e2` can be captured by the king. -/
theorem king_undefended_capture : isLegal (defendedPos []) (mv 4 1 4 2) = true := by
  kernel_fact

/-! ### Global regression: Kiwipete -/

/-- The "Kiwipete" position (Peter McKenzie),
FEN `r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1`. -/
def kiwipete : Position :=
  posWith
    [(sq 0 8, ⟨.black, .rook⟩), (sq 4 8, ⟨.black, .king⟩), (sq 7 8, ⟨.black, .rook⟩),
     (sq 0 7, ⟨.black, .pawn⟩), (sq 2 7, ⟨.black, .pawn⟩), (sq 3 7, ⟨.black, .pawn⟩),
     (sq 4 7, ⟨.black, .queen⟩), (sq 5 7, ⟨.black, .pawn⟩), (sq 6 7, ⟨.black, .bishop⟩),
     (sq 0 6, ⟨.black, .bishop⟩), (sq 1 6, ⟨.black, .knight⟩), (sq 4 6, ⟨.black, .pawn⟩),
     (sq 5 6, ⟨.black, .knight⟩), (sq 6 6, ⟨.black, .pawn⟩),
     (sq 3 5, ⟨.white, .pawn⟩), (sq 4 5, ⟨.white, .knight⟩),
     (sq 1 4, ⟨.black, .pawn⟩), (sq 4 4, ⟨.white, .pawn⟩),
     (sq 2 3, ⟨.white, .knight⟩), (sq 5 3, ⟨.white, .queen⟩), (sq 7 3, ⟨.black, .pawn⟩),
     (sq 0 2, ⟨.white, .pawn⟩), (sq 1 2, ⟨.white, .pawn⟩), (sq 2 2, ⟨.white, .pawn⟩),
     (sq 3 2, ⟨.white, .bishop⟩), (sq 4 2, ⟨.white, .bishop⟩), (sq 5 2, ⟨.white, .pawn⟩),
     (sq 6 2, ⟨.white, .pawn⟩), (sq 7 2, ⟨.white, .pawn⟩),
     (sq 0 1, ⟨.white, .rook⟩), (sq 4 1, ⟨.white, .king⟩), (sq 7 1, ⟨.white, .rook⟩)]
    .white .all

/-- 48 legal moves in Kiwipete (`S-3`; values from
<https://www.chessprogramming.org/Perft_Results>, Position 2). -/
theorem kiwipete_perft_one : perft 1 kiwipete = 48 := by kernel_fact

/-- 2 039 legal two-move sequences from Kiwipete (`S-3`;
<https://www.chessprogramming.org/Perft_Results>, Position 2). -/
theorem kiwipete_perft_two : perft 2 kiwipete = 2039 := by kernel_fact

end LeanTheory.Sanity.Chess.SpecialMoves
