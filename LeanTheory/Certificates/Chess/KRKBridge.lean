/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Certificates.Chess.KRKData
public import LeanTheory.Certificates.Chess.KQKBridge

/-!
# From a checked KRK table to forced mates in all KRK positions

Bridge for note `N-10`, the rook analogue of `KQKBridge`. Given a table `T` all of whose entries
pass `krkStateOK` and the coverage check `krkCoverOK` (defined with the data in `KRKData`), every
KRK position with White to move and the black king not attacked is a forced mate for White within
16 moves (`krk_forcesMate_of_table`), and so is every well-formed position with exactly these
three pieces, White to move and no castling rights (`krk_forcesMate_of_table_wellFormed`).
`find?_eq_of_unique` is reused from `KQKBridge`.
-/

@[expose] public section

namespace LeanTheory.Chess

/-- **KRK forced mate from a checked table**: if every entry of `T` passes `krkStateOK` and
`krkCoverOK`, then from every position with white king `wk`, white rook `wq` and black king `bk` on
distinct squares, White to move and the black king not attacked, White forces checkmate within 16
moves, whatever the halfmove clock. -/
theorem krk_forcesMate_of_table (T : Nat → Nat)
    (hT : ∀ i, i < 262144 → krkStateOK T i = true ∧ krkCoverOK T i = true)
    (wk wq bk : Square) (h₁ : wk ≠ wq) (h₂ : wk ≠ bk) (h₃ : wq ≠ bk)
    (hc : attackedBy (krkBoard wk wq bk) .white bk = false) (h : Nat) :
    ForcesMate .white 16 (krkPos wk wq bk .white h) := by
  have hi : kqkIdx wk.val wq.val bk.val < 262144 := by
    have := wk.isLt; have := wq.isLt; have := bk.isLt; simp only [kqkIdx]; omega
  obtain ⟨hs, hcov⟩ := hT _ hi
  obtain ⟨e₁, e₂, e₃⟩ := sqOf_kqkIdx wk wq bk
  simp only [krkCoverOK, e₁, e₂, e₃, hc, Bool.or_eq_true, beq_iff_eq, h₁, h₂, h₃, false_or,
    bne_iff_ne, ne_eq, Bool.false_eq_true] at hcov
  have hle : krkDepth (T (kqkIdx wk.val wq.val bk.val)) ≤ 16 := by
    simp only [krkStateOK, Bool.or_eq_true, beq_iff_eq, hcov, false_or, Bool.and_eq_true,
      decide_eq_true_eq] at hs
    exact hs.1.1.1.1
  have hm := krk_table_sound T (fun i hi => (hT i hi).1) _ wk wq bk rfl hcov h
  have := hm.mono (16 - krkDepth (T (kqkIdx wk.val wq.val bk.val)))
  rwa [Nat.add_sub_cancel' hle] at this

/-- The black king of a KRK board is found on `bk`. -/
theorem kingSquare_krk_black (wk wq bk : Square) (h₂ : wk ≠ bk) (h₃ : wq ≠ bk) :
    kingSquare (krkBoard wk wq bk) .black = some bk := by
  refine find?_eq_of_unique (mem_allSquares bk) ?_ fun y _ hy => ?_
  · simp [krkBoard, Ne.symm h₂, Ne.symm h₃]
  · simp only [krkBoard, beq_iff_eq] at hy
    split_ifs at hy <;> simp_all

/-- No pawn stands on a KRK board. -/
theorem krkBoard_ne_pawn (wk wq bk s : Square) (c : Color) :
    krkBoard wk wq bk s ≠ some ⟨c, .pawn⟩ := by
  unfold krkBoard
  split_ifs <;> simp

/-- A well-formed position on a KRK board has no en passant target. -/
theorem epTarget_eq_none_of_krk {p : Position} {wk wq bk : Square}
    (hb : p.board = krkBoard wk wq bk) (hw : wellFormed p = true) : p.epTarget = none := by
  simp only [wellFormed, Bool.and_eq_true] at hw
  have he := hw.2
  unfold epConsistent at he
  cases ht : p.epTarget with
  | none => rfl
  | some t =>
    rw [ht] at he
    simp only [Bool.and_eq_true] at he
    obtain ⟨⟨_, hu⟩, _⟩ := he
    split at hu
    · rename_i u _
      simp only [hb, beq_iff_eq] at hu
      exact absurd hu (krkBoard_ne_pawn _ _ _ _ _)
    · exact absurd hu Bool.false_ne_true

/-- **KRK forced mate for well-formed positions, from a checked table**: every well-formed position
whose pieces are a white king on `wk`, a white rook on `wq` and a black king on `bk`, with White
to move and no castling rights, is a forced mate for White within 16 moves. -/
theorem krk_forcesMate_of_table_wellFormed (T : Nat → Nat)
    (hT : ∀ i, i < 262144 → krkStateOK T i = true ∧ krkCoverOK T i = true)
    (p : Position) (wk wq bk : Square) (h₁ : wk ≠ wq) (h₂ : wk ≠ bk) (h₃ : wq ≠ bk)
    (hb : p.board = krkBoard wk wq bk) (ht : p.turn = .white) (hcr : p.castling = .none)
    (hw : wellFormed p = true) : ForcesMate .white 16 p := by
  have hep := epTarget_eq_none_of_krk hb hw
  have hc : attackedBy (krkBoard wk wq bk) .white bk = false := by
    simp only [wellFormed, Bool.and_eq_true, Bool.not_eq_true'] at hw
    have := hw.1.2
    rw [ht, hb] at this
    simpa [inCheck, Color.other, kingSquare_krk_black wk wq bk h₂ h₃] using this
  have hp : p = krkPos wk wq bk .white p.halfmove := by
    cases p; simp_all [krkPos]
  rw [hp]
  exact krk_forcesMate_of_table T hT wk wq bk h₁ h₂ h₃ hc p.halfmove

end LeanTheory.Chess
