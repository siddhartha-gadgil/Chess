/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Certificates.Chess.KRKBridge
public import LeanTheory.Certificates.Chess.KRKBlackGame
public import LeanTheory.Certificates.Chess.KRKChunks.C00
public import LeanTheory.Certificates.Chess.KRKChunks.C01
public import LeanTheory.Certificates.Chess.KRKChunks.C02
public import LeanTheory.Certificates.Chess.KRKChunks.C03
public import LeanTheory.Certificates.Chess.KRKChunks.C04
public import LeanTheory.Certificates.Chess.KRKChunks.C05
public import LeanTheory.Certificates.Chess.KRKChunks.C06
public import LeanTheory.Certificates.Chess.KRKChunks.C07
public import LeanTheory.Certificates.Chess.KRKChunks.C08
public import LeanTheory.Certificates.Chess.KRKChunks.C09
public import LeanTheory.Certificates.Chess.KRKChunks.C10
public import LeanTheory.Certificates.Chess.KRKChunks.C11
public import LeanTheory.Certificates.Chess.KRKChunks.C12
public import LeanTheory.Certificates.Chess.KRKChunks.C13
public import LeanTheory.Certificates.Chess.KRKChunks.C14
public import LeanTheory.Certificates.Chess.KRKChunks.C15
public import LeanTheory.Certificates.Chess.KRKChunks.C16
public import LeanTheory.Certificates.Chess.KRKChunks.C17
public import LeanTheory.Certificates.Chess.KRKChunks.C18
public import LeanTheory.Certificates.Chess.KRKChunks.C19
public import LeanTheory.Certificates.Chess.KRKChunks.C20
public import LeanTheory.Certificates.Chess.KRKChunks.C21
public import LeanTheory.Certificates.Chess.KRKChunks.C22
public import LeanTheory.Certificates.Chess.KRKChunks.C23
public import LeanTheory.Certificates.Chess.KRKChunks.C24
public import LeanTheory.Certificates.Chess.KRKChunks.C25
public import LeanTheory.Certificates.Chess.KRKChunks.C26
public import LeanTheory.Certificates.Chess.KRKChunks.C27
public import LeanTheory.Certificates.Chess.KRKChunks.C28
public import LeanTheory.Certificates.Chess.KRKChunks.C29
public import LeanTheory.Certificates.Chess.KRKChunks.C30
public import LeanTheory.Certificates.Chess.KRKChunks.C31
public import LeanTheory.Certificates.Chess.KRKChunks.C32
public import LeanTheory.Certificates.Chess.KRKChunks.C33
public import LeanTheory.Certificates.Chess.KRKChunks.C34
public import LeanTheory.Certificates.Chess.KRKChunks.C35
public import LeanTheory.Certificates.Chess.KRKChunks.C36
public import LeanTheory.Certificates.Chess.KRKChunks.C37
public import LeanTheory.Certificates.Chess.KRKChunks.C38
public import LeanTheory.Certificates.Chess.KRKChunks.C39
public import LeanTheory.Certificates.Chess.KRKChunks.C40
public import LeanTheory.Certificates.Chess.KRKChunks.C41
public import LeanTheory.Certificates.Chess.KRKChunks.C42
public import LeanTheory.Certificates.Chess.KRKChunks.C43
public import LeanTheory.Certificates.Chess.KRKChunks.C44
public import LeanTheory.Certificates.Chess.KRKChunks.C45
public import LeanTheory.Certificates.Chess.KRKChunks.C46
public import LeanTheory.Certificates.Chess.KRKChunks.C47
public import LeanTheory.Certificates.Chess.KRKChunks.C48
public import LeanTheory.Certificates.Chess.KRKChunks.C49
public import LeanTheory.Certificates.Chess.KRKChunks.C50
public import LeanTheory.Certificates.Chess.KRKChunks.C51
public import LeanTheory.Certificates.Chess.KRKChunks.C52
public import LeanTheory.Certificates.Chess.KRKChunks.C53
public import LeanTheory.Certificates.Chess.KRKChunks.C54
public import LeanTheory.Certificates.Chess.KRKChunks.C55
public import LeanTheory.Certificates.Chess.KRKChunks.C56
public import LeanTheory.Certificates.Chess.KRKChunks.C57
public import LeanTheory.Certificates.Chess.KRKChunks.C58
public import LeanTheory.Certificates.Chess.KRKChunks.C59
public import LeanTheory.Certificates.Chess.KRKChunks.C60
public import LeanTheory.Certificates.Chess.KRKChunks.C61
public import LeanTheory.Certificates.Chess.KRKChunks.C62
public import LeanTheory.Certificates.Chess.KRKChunks.C63

/-!
# King and rook versus king: a forced win (note `N-10`)

**Main theorems**:

* `krk_forcesMate`: from every position with a white king, a white rook and a black king on
  distinct squares, White to move and the black king not attacked, White forces checkmate within
  16 moves against every defence (any halfmove clock);
* `krk_forcesMate_wellFormed`: the same for every well-formed `Position` whose pieces are exactly
  these three, with White to move and no castling rights;
* `krk_black_to_move`: with Black to move, Black is mated, stalemated, can capture the rook into a
  dead position, or White forces mate within 16 moves;
* `krk_game_whiteWins_wellFormed`: in the full game `chessGame` (all automatic draw rules), from a
  fresh start with clock at most 118, White forces a win and the value is `whiteWins`.

Proof: an untrusted retrograde analysis supplied a table of depths and White moves (`KRKData`);
the 64 chunk modules check every entry by kernel evaluation (`krk_chunk_0` … `krk_chunk_63`, no
`decide`); `krk_table_sound` and the bridge `krk_forcesMate_of_table` turn the check into forced
mates.

The last two are the instances, for the checked table, of the conditional results of
`KRKBlackGame`.
-/

@[expose] public section

namespace LeanTheory.Chess

/-- Every chunk of the KRK table passes the check. -/
theorem krkChunkOK_all : ∀ wk, wk < 64 → krkChunkOK wk = true
  | 0, _ => krk_chunk_0
  | 1, _ => krk_chunk_1
  | 2, _ => krk_chunk_2
  | 3, _ => krk_chunk_3
  | 4, _ => krk_chunk_4
  | 5, _ => krk_chunk_5
  | 6, _ => krk_chunk_6
  | 7, _ => krk_chunk_7
  | 8, _ => krk_chunk_8
  | 9, _ => krk_chunk_9
  | 10, _ => krk_chunk_10
  | 11, _ => krk_chunk_11
  | 12, _ => krk_chunk_12
  | 13, _ => krk_chunk_13
  | 14, _ => krk_chunk_14
  | 15, _ => krk_chunk_15
  | 16, _ => krk_chunk_16
  | 17, _ => krk_chunk_17
  | 18, _ => krk_chunk_18
  | 19, _ => krk_chunk_19
  | 20, _ => krk_chunk_20
  | 21, _ => krk_chunk_21
  | 22, _ => krk_chunk_22
  | 23, _ => krk_chunk_23
  | 24, _ => krk_chunk_24
  | 25, _ => krk_chunk_25
  | 26, _ => krk_chunk_26
  | 27, _ => krk_chunk_27
  | 28, _ => krk_chunk_28
  | 29, _ => krk_chunk_29
  | 30, _ => krk_chunk_30
  | 31, _ => krk_chunk_31
  | 32, _ => krk_chunk_32
  | 33, _ => krk_chunk_33
  | 34, _ => krk_chunk_34
  | 35, _ => krk_chunk_35
  | 36, _ => krk_chunk_36
  | 37, _ => krk_chunk_37
  | 38, _ => krk_chunk_38
  | 39, _ => krk_chunk_39
  | 40, _ => krk_chunk_40
  | 41, _ => krk_chunk_41
  | 42, _ => krk_chunk_42
  | 43, _ => krk_chunk_43
  | 44, _ => krk_chunk_44
  | 45, _ => krk_chunk_45
  | 46, _ => krk_chunk_46
  | 47, _ => krk_chunk_47
  | 48, _ => krk_chunk_48
  | 49, _ => krk_chunk_49
  | 50, _ => krk_chunk_50
  | 51, _ => krk_chunk_51
  | 52, _ => krk_chunk_52
  | 53, _ => krk_chunk_53
  | 54, _ => krk_chunk_54
  | 55, _ => krk_chunk_55
  | 56, _ => krk_chunk_56
  | 57, _ => krk_chunk_57
  | 58, _ => krk_chunk_58
  | 59, _ => krk_chunk_59
  | 60, _ => krk_chunk_60
  | 61, _ => krk_chunk_61
  | 62, _ => krk_chunk_62
  | 63, _ => krk_chunk_63
  | _ + 64, h => absurd h (by omega)

/-- Every entry of the KRK table passes `krkStateOK` and `krkCoverOK`. -/
theorem krkTable_ok (i : Nat) (hi : i < 262144) :
    krkStateOK krkTable i = true ∧ krkCoverOK krkTable i = true := by
  have hc := krkChunkOK_all (i / 4096) (by omega)
  simp only [krkChunkOK, krkRowOK, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hc
  have := hc (i / 64 % 64) (Nat.mod_lt _ (by omega)) (i % 64) (Nat.mod_lt _ (by omega))
  rwa [show i / 4096 * 4096 + i / 64 % 64 * 64 + i % 64 = i by omega] at this

/-- **King and rook versus king is a forced win** (note `N-10`): with White to move, from every
position with the white king on `wk`, the white rook on `wq` and the black king on `bk` (distinct
squares, black king not attacked), White forces checkmate within 16 moves. -/
theorem krk_forcesMate (wk wq bk : Square) (h₁ : wk ≠ wq) (h₂ : wk ≠ bk) (h₃ : wq ≠ bk)
    (hc : attackedBy (krkBoard wk wq bk) .white bk = false) (h : Nat) :
    ForcesMate .white 16 (krkPos wk wq bk .white h) :=
  krk_forcesMate_of_table krkTable krkTable_ok wk wq bk h₁ h₂ h₃ hc h

/-- **King and rook versus king, for well-formed positions**: every well-formed position whose
pieces are a white king, a white rook and a black king, with White to move and no castling
rights, is a forced mate for White within 16 moves. -/
theorem krk_forcesMate_wellFormed (p : Position) (wk wq bk : Square) (h₁ : wk ≠ wq)
    (h₂ : wk ≠ bk) (h₃ : wq ≠ bk) (hb : p.board = krkBoard wk wq bk) (ht : p.turn = .white)
    (hcr : p.castling = .none) (hw : wellFormed p = true) : ForcesMate .white 16 p :=
  krk_forcesMate_of_table_wellFormed krkTable krkTable_ok p wk wq bk h₁ h₂ h₃ hb ht hcr hw

/-- **King and rook versus king, Black to move**: in every well-formed KRK position with Black to
move and no castling rights, Black is checkmated, or stalemated, or has a legal capture of the
rook reaching a dead position, or White forces mate within 16 moves. -/
theorem krk_black_to_move (p : Position) (wk wq bk : Square) (h₁ : wk ≠ wq) (h₂ : wk ≠ bk)
    (h₃ : wq ≠ bk) (hb : p.board = krkBoard wk wq bk) (ht : p.turn = .black)
    (hcr : p.castling = .none) (hw : wellFormed p = true) :
    isCheckmate p = true ∨ isStalemate p = true ∨
      (∃ m ∈ legalMoves p, m.dst = wq ∧ IsDead (play p m)) ∨ ForcesMate .white 16 p :=
  krk_black_to_move_of_table krkTable krkTable_ok p wk wq bk h₁ h₂ h₃ hb ht hcr hw

/-- **King and rook versus king in the full game**: from the start of a game in a well-formed KRK
position with White to move, no castling rights and halfmove clock at most 118, White can force
a win in `chessGame`, whose value there is `whiteWins`. -/
theorem krk_game_whiteWins_wellFormed (p : Position) (a b c : Square) (h₁ : a ≠ b) (h₂ : a ≠ c)
    (h₃ : b ≠ c) (hb : p.board = krkBoard a b c) (ht : p.turn = .white)
    (hcr : p.castling = .none) (hw : wellFormed p = true) (hh : p.halfmove ≤ 118) :
    chessGame.MaxForces .whiteWins (State.start p) ∧
      chessGame.value (State.start p) = .whiteWins :=
  krk_game_whiteWins_of_table_wellFormed krkTable krkTable_ok p a b c h₁ h₂ h₃ hb ht hcr hw hh

end LeanTheory.Chess
