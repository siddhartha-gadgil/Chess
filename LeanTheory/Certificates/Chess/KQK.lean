/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Certificates.Chess.KQKBridge
public import LeanTheory.Certificates.Chess.KQKChunks.C00
public import LeanTheory.Certificates.Chess.KQKChunks.C01
public import LeanTheory.Certificates.Chess.KQKChunks.C02
public import LeanTheory.Certificates.Chess.KQKChunks.C03
public import LeanTheory.Certificates.Chess.KQKChunks.C04
public import LeanTheory.Certificates.Chess.KQKChunks.C05
public import LeanTheory.Certificates.Chess.KQKChunks.C06
public import LeanTheory.Certificates.Chess.KQKChunks.C07
public import LeanTheory.Certificates.Chess.KQKChunks.C08
public import LeanTheory.Certificates.Chess.KQKChunks.C09
public import LeanTheory.Certificates.Chess.KQKChunks.C10
public import LeanTheory.Certificates.Chess.KQKChunks.C11
public import LeanTheory.Certificates.Chess.KQKChunks.C12
public import LeanTheory.Certificates.Chess.KQKChunks.C13
public import LeanTheory.Certificates.Chess.KQKChunks.C14
public import LeanTheory.Certificates.Chess.KQKChunks.C15
public import LeanTheory.Certificates.Chess.KQKChunks.C16
public import LeanTheory.Certificates.Chess.KQKChunks.C17
public import LeanTheory.Certificates.Chess.KQKChunks.C18
public import LeanTheory.Certificates.Chess.KQKChunks.C19
public import LeanTheory.Certificates.Chess.KQKChunks.C20
public import LeanTheory.Certificates.Chess.KQKChunks.C21
public import LeanTheory.Certificates.Chess.KQKChunks.C22
public import LeanTheory.Certificates.Chess.KQKChunks.C23
public import LeanTheory.Certificates.Chess.KQKChunks.C24
public import LeanTheory.Certificates.Chess.KQKChunks.C25
public import LeanTheory.Certificates.Chess.KQKChunks.C26
public import LeanTheory.Certificates.Chess.KQKChunks.C27
public import LeanTheory.Certificates.Chess.KQKChunks.C28
public import LeanTheory.Certificates.Chess.KQKChunks.C29
public import LeanTheory.Certificates.Chess.KQKChunks.C30
public import LeanTheory.Certificates.Chess.KQKChunks.C31
public import LeanTheory.Certificates.Chess.KQKChunks.C32
public import LeanTheory.Certificates.Chess.KQKChunks.C33
public import LeanTheory.Certificates.Chess.KQKChunks.C34
public import LeanTheory.Certificates.Chess.KQKChunks.C35
public import LeanTheory.Certificates.Chess.KQKChunks.C36
public import LeanTheory.Certificates.Chess.KQKChunks.C37
public import LeanTheory.Certificates.Chess.KQKChunks.C38
public import LeanTheory.Certificates.Chess.KQKChunks.C39
public import LeanTheory.Certificates.Chess.KQKChunks.C40
public import LeanTheory.Certificates.Chess.KQKChunks.C41
public import LeanTheory.Certificates.Chess.KQKChunks.C42
public import LeanTheory.Certificates.Chess.KQKChunks.C43
public import LeanTheory.Certificates.Chess.KQKChunks.C44
public import LeanTheory.Certificates.Chess.KQKChunks.C45
public import LeanTheory.Certificates.Chess.KQKChunks.C46
public import LeanTheory.Certificates.Chess.KQKChunks.C47
public import LeanTheory.Certificates.Chess.KQKChunks.C48
public import LeanTheory.Certificates.Chess.KQKChunks.C49
public import LeanTheory.Certificates.Chess.KQKChunks.C50
public import LeanTheory.Certificates.Chess.KQKChunks.C51
public import LeanTheory.Certificates.Chess.KQKChunks.C52
public import LeanTheory.Certificates.Chess.KQKChunks.C53
public import LeanTheory.Certificates.Chess.KQKChunks.C54
public import LeanTheory.Certificates.Chess.KQKChunks.C55
public import LeanTheory.Certificates.Chess.KQKChunks.C56
public import LeanTheory.Certificates.Chess.KQKChunks.C57
public import LeanTheory.Certificates.Chess.KQKChunks.C58
public import LeanTheory.Certificates.Chess.KQKChunks.C59
public import LeanTheory.Certificates.Chess.KQKChunks.C60
public import LeanTheory.Certificates.Chess.KQKChunks.C61
public import LeanTheory.Certificates.Chess.KQKChunks.C62
public import LeanTheory.Certificates.Chess.KQKChunks.C63

/-!
# King and queen versus king: a forced win (goal `G-2`)

**Main theorems** (note `N-05`):

* `kqk_forcesMate`: from every position with a white king, a white queen and a black king on
  distinct squares, White to move and the black king not attacked, White forces checkmate within
  10 moves against every defence (any halfmove clock);
* `kqk_forcesMate_wellFormed`: the same for every well-formed `Position` whose pieces are exactly
  these three, with White to move and no castling rights.

Proof: an untrusted retrograde analysis (`N-06`) supplied a table of depths and White moves
(`KQKData`); the 64 chunk modules check every entry by kernel evaluation (`kqk_chunk_0` …
`kqk_chunk_63`, no `decide`); `table_sound` and the bridge `kqk_forcesMate_of_table` turn the check
into forced mates.

Scope: `ForcesMate` is about positions (rung (i) of the model ladder): it ignores the draw rules
that depend on the game history. Since a forced mate within 10 moves takes at most 19 plies, the
75-move and fivefold rules can only interfere from a game state whose history is already near
those limits; the transfer to `GameState` is a separate lemma (not yet proved).
-/

@[expose] public section

namespace LeanTheory.Chess

/-- Every chunk of the KQK table passes the check. -/
theorem chunkOK_all : ∀ wk, wk < 64 → chunkOK wk = true
  | 0, _ => kqk_chunk_0
  | 1, _ => kqk_chunk_1
  | 2, _ => kqk_chunk_2
  | 3, _ => kqk_chunk_3
  | 4, _ => kqk_chunk_4
  | 5, _ => kqk_chunk_5
  | 6, _ => kqk_chunk_6
  | 7, _ => kqk_chunk_7
  | 8, _ => kqk_chunk_8
  | 9, _ => kqk_chunk_9
  | 10, _ => kqk_chunk_10
  | 11, _ => kqk_chunk_11
  | 12, _ => kqk_chunk_12
  | 13, _ => kqk_chunk_13
  | 14, _ => kqk_chunk_14
  | 15, _ => kqk_chunk_15
  | 16, _ => kqk_chunk_16
  | 17, _ => kqk_chunk_17
  | 18, _ => kqk_chunk_18
  | 19, _ => kqk_chunk_19
  | 20, _ => kqk_chunk_20
  | 21, _ => kqk_chunk_21
  | 22, _ => kqk_chunk_22
  | 23, _ => kqk_chunk_23
  | 24, _ => kqk_chunk_24
  | 25, _ => kqk_chunk_25
  | 26, _ => kqk_chunk_26
  | 27, _ => kqk_chunk_27
  | 28, _ => kqk_chunk_28
  | 29, _ => kqk_chunk_29
  | 30, _ => kqk_chunk_30
  | 31, _ => kqk_chunk_31
  | 32, _ => kqk_chunk_32
  | 33, _ => kqk_chunk_33
  | 34, _ => kqk_chunk_34
  | 35, _ => kqk_chunk_35
  | 36, _ => kqk_chunk_36
  | 37, _ => kqk_chunk_37
  | 38, _ => kqk_chunk_38
  | 39, _ => kqk_chunk_39
  | 40, _ => kqk_chunk_40
  | 41, _ => kqk_chunk_41
  | 42, _ => kqk_chunk_42
  | 43, _ => kqk_chunk_43
  | 44, _ => kqk_chunk_44
  | 45, _ => kqk_chunk_45
  | 46, _ => kqk_chunk_46
  | 47, _ => kqk_chunk_47
  | 48, _ => kqk_chunk_48
  | 49, _ => kqk_chunk_49
  | 50, _ => kqk_chunk_50
  | 51, _ => kqk_chunk_51
  | 52, _ => kqk_chunk_52
  | 53, _ => kqk_chunk_53
  | 54, _ => kqk_chunk_54
  | 55, _ => kqk_chunk_55
  | 56, _ => kqk_chunk_56
  | 57, _ => kqk_chunk_57
  | 58, _ => kqk_chunk_58
  | 59, _ => kqk_chunk_59
  | 60, _ => kqk_chunk_60
  | 61, _ => kqk_chunk_61
  | 62, _ => kqk_chunk_62
  | 63, _ => kqk_chunk_63
  | _ + 64, h => absurd h (by omega)

/-- Every entry of the KQK table passes `stateOK` and `coverOK`. -/
theorem kqkTable_ok (i : Nat) (hi : i < 262144) :
    stateOK kqkTable i = true ∧ coverOK kqkTable i = true := by
  have hc := chunkOK_all (i / 4096) (by omega)
  simp only [chunkOK, rowOK, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hc
  have := hc (i / 64 % 64) (Nat.mod_lt _ (by omega)) (i % 64) (Nat.mod_lt _ (by omega))
  rwa [show i / 4096 * 4096 + i / 64 % 64 * 64 + i % 64 = i by omega] at this

/-- **King and queen versus king is a forced win** (goal `G-2`): with White to move, from every
position with the white king on `wk`, the white queen on `wq` and the black king on `bk` (distinct
squares, black king not attacked), White forces checkmate within 10 moves. -/
theorem kqk_forcesMate (wk wq bk : Square) (h₁ : wk ≠ wq) (h₂ : wk ≠ bk) (h₃ : wq ≠ bk)
    (hc : attackedBy (kqkBoard wk wq bk) .white bk = false) (h : Nat) :
    ForcesMate .white 10 (kqkPos wk wq bk .white h) :=
  kqk_forcesMate_of_table kqkTable kqkTable_ok wk wq bk h₁ h₂ h₃ hc h

/-- **King and queen versus king, for well-formed positions**: every well-formed position whose
pieces are a white king, a white queen and a black king, with White to move and no castling
rights, is a forced mate for White within 10 moves. -/
theorem kqk_forcesMate_wellFormed (p : Position) (wk wq bk : Square) (h₁ : wk ≠ wq)
    (h₂ : wk ≠ bk) (h₃ : wq ≠ bk) (hb : p.board = kqkBoard wk wq bk) (ht : p.turn = .white)
    (hcr : p.castling = .none) (hw : wellFormed p = true) : ForcesMate .white 10 p :=
  kqk_forcesMate_of_table_wellFormed kqkTable kqkTable_ok p wk wq bk h₁ h₂ h₃ hb ht hcr hw

end LeanTheory.Chess
