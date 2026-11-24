/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Certificates.Chess.KQKData

/-!
# From a checked KQK table to forced mates in all KQK positions

Bridge for goal `G-2` (note `N-05`). Given a table `T` all of whose entries pass `stateOK` and
the coverage check `coverOK` (defined with the data in `KQKData`), every KQK position with White
to move and the black king not attacked is a forced mate for White within 10 moves
(`kqk_forcesMate_of_table`), and so is every well-formed
position with exactly these three pieces, White to move and no castling rights
(`kqk_forcesMate_of_table_wellFormed`). The table itself is supplied and checked in
`Certificates/Chess/KQK`.
-/

@[expose] public section

namespace LeanTheory.Chess

/-- **KQK forced mate from a checked table**: if every entry of `T` passes `stateOK` and
`coverOK`, then from every position with white king `wk`, white queen `wq` and black king `bk` on
distinct squares, White to move and the black king not attacked, White forces checkmate within 10
moves, whatever the halfmove clock. -/
theorem kqk_forcesMate_of_table (T : Nat → Nat)
    (hT : ∀ i, i < 262144 → stateOK T i = true ∧ coverOK T i = true)
    (wk wq bk : Square) (h₁ : wk ≠ wq) (h₂ : wk ≠ bk) (h₃ : wq ≠ bk)
    (hc : attackedBy (kqkBoard wk wq bk) .white bk = false) (h : Nat) :
    ForcesMate .white 10 (kqkPos wk wq bk .white h) := by
  have hi : kqkIdx wk.val wq.val bk.val < 262144 := by
    have := wk.isLt; have := wq.isLt; have := bk.isLt; simp only [kqkIdx]; omega
  obtain ⟨hs, hcov⟩ := hT _ hi
  obtain ⟨e₁, e₂, e₃⟩ := sqOf_kqkIdx wk wq bk
  simp only [coverOK, e₁, e₂, e₃, hc, Bool.or_eq_true, beq_iff_eq, h₁, h₂, h₃, false_or,
    bne_iff_ne, ne_eq, Bool.false_eq_true] at hcov
  have hle : entDepth (T (kqkIdx wk.val wq.val bk.val)) ≤ 10 := by
    simp only [stateOK, Bool.or_eq_true, beq_iff_eq, hcov, false_or, Bool.and_eq_true,
      decide_eq_true_eq] at hs
    exact hs.1.1.1.1
  have hm := table_sound T (fun i hi => (hT i hi).1) _ wk wq bk rfl hcov h
  have := hm.mono (10 - entDepth (T (kqkIdx wk.val wq.val bk.val)))
  rwa [Nat.add_sub_cancel' hle] at this

/-- If only `x` satisfies `p` in `l` and `x ∈ l`, then `find?` returns `x`. -/
theorem find?_eq_of_unique {α : Type} {l : List α} {p : α → Bool} {x : α} (hx : x ∈ l)
    (hp : p x = true) (hu : ∀ y ∈ l, p y = true → y = x) : l.find? p = some x := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    by_cases ha : p a = true
    · rw [List.find?_cons_of_pos ha, hu a (by simp) ha]
    · rw [List.find?_cons_of_neg ha]
      rcases List.mem_cons.1 hx with rfl | hx
      · exact absurd hp ha
      · exact ih hx fun y hy => hu y (List.mem_cons_of_mem a hy)

/-- The black king of a KQK board is found on `bk`. -/
theorem kingSquare_kqk_black (wk wq bk : Square) (h₂ : wk ≠ bk) (h₃ : wq ≠ bk) :
    kingSquare (kqkBoard wk wq bk) .black = some bk := by
  refine find?_eq_of_unique (mem_allSquares bk) ?_ fun y _ hy => ?_
  · simp [kqkBoard, Ne.symm h₂, Ne.symm h₃]
  · simp only [kqkBoard, beq_iff_eq] at hy
    split_ifs at hy <;> simp_all

/-- No pawn stands on a KQK board. -/
theorem kqkBoard_ne_pawn (wk wq bk s : Square) (c : Color) :
    kqkBoard wk wq bk s ≠ some ⟨c, .pawn⟩ := by
  unfold kqkBoard
  split_ifs <;> simp

/-- A well-formed position on a KQK board has no en passant target. -/
theorem epTarget_eq_none_of_kqk {p : Position} {wk wq bk : Square}
    (hb : p.board = kqkBoard wk wq bk) (hw : wellFormed p = true) : p.epTarget = none := by
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
      exact absurd hu (kqkBoard_ne_pawn _ _ _ _ _)
    · exact absurd hu Bool.false_ne_true

/-- **KQK forced mate for well-formed positions, from a checked table**: every well-formed position
whose pieces are a white king on `wk`, a white queen on `wq` and a black king on `bk`, with White
to move and no castling rights, is a forced mate for White within 10 moves. -/
theorem kqk_forcesMate_of_table_wellFormed (T : Nat → Nat)
    (hT : ∀ i, i < 262144 → stateOK T i = true ∧ coverOK T i = true)
    (p : Position) (wk wq bk : Square) (h₁ : wk ≠ wq) (h₂ : wk ≠ bk) (h₃ : wq ≠ bk)
    (hb : p.board = kqkBoard wk wq bk) (ht : p.turn = .white) (hcr : p.castling = .none)
    (hw : wellFormed p = true) : ForcesMate .white 10 p := by
  have hep := epTarget_eq_none_of_kqk hb hw
  have hc : attackedBy (kqkBoard wk wq bk) .white bk = false := by
    simp only [wellFormed, Bool.and_eq_true, Bool.not_eq_true'] at hw
    have := hw.1.2
    rw [ht, hb] at this
    simpa [inCheck, Color.other, kingSquare_kqk_black wk wq bk h₂ h₃] using this
  have hp : p = kqkPos wk wq bk .white p.halfmove := by
    cases p; simp_all [kqkPos]
  rw [hp]
  exact kqk_forcesMate_of_table T hT wk wq bk h₁ h₂ h₃ hc p.halfmove

end LeanTheory.Chess
