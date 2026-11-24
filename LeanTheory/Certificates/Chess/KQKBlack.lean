/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Certificates.Chess.KQK
public import LeanTheory.Theory.Chess.DeadPositions

/-!
# King and queen versus king with Black to move

Note `N-05`, goal `G-2`: the Black-to-move case split. In a well-formed position whose pieces are
a white king on `wk`, a white queen on `wq` and a black king on `bk`, with Black to move and no
castling rights (`kqk_black_to_move`), exactly one of the following happens:

* Black is checkmated or stalemated (no legal move);
* Black can capture the queen; the capture leaves two non-adjacent bare kings, a dead position
  (`kqk_black_capture_dead`, via the invariant `KKInv` of `Theory/Chess/DeadPositions`);
* otherwise every legal Black move is a non-capturing king step to a KQK position with White to
  move and the black king not attacked, so White forces mate within 10 moves
  (`kqk_black_forcesMate`, from `kqk_forcesMate`).

The argument is symbolic: on a KQK board with Black to move every pseudo-legal move is a king step
of the black king (`mem_pseudoMoves_kqk_black`), it never lands on the white king since the kings
are not adjacent (`kingAdj_eq_false_of_kqk`), and its effect is computed by `play_kqk_black` or
`play_board_kingMove`. Fixtures exhibit one position of each kind.
-/

@[expose] public section

namespace LeanTheory.Chess

/-! ### Kings on KQK boards -/

/-- The black king of a KQK board (distinct squares) stands exactly on `bk`. -/
theorem kqkBoard_eq_black_king {wk wq bk : Square} (h₂ : wk ≠ bk) (h₃ : wq ≠ bk) (u : Square) :
    kqkBoard wk wq bk u = some ⟨.black, .king⟩ ↔ u = bk := by
  unfold kqkBoard; split_ifs <;> simp_all

/-- The white king of a KQK board stands exactly on `wk`. -/
theorem kqkBoard_eq_white_king {wk wq bk : Square} (u : Square) :
    kqkBoard wk wq bk u = some ⟨.white, .king⟩ ↔ u = wk := by
  unfold kqkBoard; split_ifs <;> simp_all

/-- The white king of a KQK board is found on `wk`. -/
theorem kingSquare_kqk_white (wk wq bk : Square) :
    kingSquare (kqkBoard wk wq bk) .white = some wk :=
  kingSquare_unique kqkBoard_eq_white_king

/-- If White is not in check on a KQK board, the kings are not adjacent. -/
theorem kingAdj_eq_false_of_kqk {wk wq bk : Square} (h₂ : wk ≠ bk) (h₃ : wq ≠ bk)
    (hc : inCheck (kqkBoard wk wq bk) .white = false) : kingAdj wk bk = false := by
  unfold inCheck at hc
  rw [kingSquare_kqk_white] at hc
  simp only [Color.other] at hc
  unfold attackedBy at hc
  rw [pieceAtOffsets_unique (kqkBoard_eq_black_king h₂ h₃)] at hc
  simp only [Bool.or_eq_false_iff] at hc
  exact hc.1.1.1.2

/-! ### Black's moves -/

/-- On a KQK board with Black to move, every pseudo-legal move is a plain step of the black
king. -/
theorem mem_pseudoMoves_kqk_black {wk wq bk : Square} {h : Nat} {m : Move}
    (hm : m ∈ pseudoMoves (kqkPos wk wq bk .black h)) :
    m.src = bk ∧ m.promo = none ∧ kingAdj bk m.dst = true := by
  have hr : castlingMoves (kqkPos wk wq bk .black h) = [] := by
    simp [castlingMoves, kqkPos, CastlingRights.kingSide, CastlingRights.queenSide,
      CastlingRights.none]
  simp only [pseudoMoves, hr, List.append_nil, List.mem_flatMap] at hm
  obtain ⟨s, -, hm⟩ := hm
  split at hm
  · rename_i pc hs
    split_ifs at hm with hc
    · obtain ⟨c, k⟩ := pc
      simp only [kqkPos] at hc hs
      subst hc
      have hk : k = .king ∧ s = bk := by
        unfold kqkBoard at hs; split_ifs at hs <;> simp_all
      obtain ⟨rfl, rfl⟩ := hk
      simp only [pieceMoves, List.mem_map] at hm
      obtain ⟨t, ht, rfl⟩ := hm
      obtain ⟨⟨d, hd, hu⟩, -⟩ := mem_stepTargets.1 ht
      refine ⟨rfl, rfl, ?_⟩
      simp only [kingAdj, List.any_eq_true, beq_iff_eq]
      exact ⟨d, hd, hu⟩
    · simp at hm
  · simp at hm

/-- A legal Black move in a KQK position with non-adjacent kings is the king step
`⟨bk, t, none⟩` to a square `t ≠ wk, bk` adjacent to `bk`, after which Black is not in check. -/
theorem legal_kqk_black {wk wq bk : Square} {h : Nat} (hadj : kingAdj wk bk = false) {m : Move}
    (hm : m ∈ legalMoves (kqkPos wk wq bk .black h)) :
    m = ⟨bk, m.dst, none⟩ ∧ kingAdj bk m.dst = true ∧ m.dst ≠ wk ∧ m.dst ≠ bk ∧
      inCheck (play (kqkPos wk wq bk .black h) m).board .black = false := by
  simp only [legalMoves, List.mem_filter, Bool.not_eq_true'] at hm
  obtain ⟨hps, hchk⟩ := hm
  obtain ⟨hs, hp, ha⟩ := mem_pseudoMoves_kqk_black hps
  refine ⟨by cases m; simp_all, ha, ?_, (kingAdj_iff.1 ha).1.symm, hchk⟩
  rintro hd
  rw [hd, kingAdj_comm, hadj] at ha
  exact Bool.false_ne_true ha

/-- **Capturing the queen gives a dead position**: if Black's legal move captures the queen on a
KQK board with non-adjacent kings, the result has two non-adjacent bare kings (`KKInv`). -/
theorem kqk_black_capture_kkInv {wk wq bk : Square} {h : Nat} (h₁ : wk ≠ wq) (h₂ : wk ≠ bk)
    (h₃ : wq ≠ bk) (hadj : kingAdj wk bk = false) {m : Move}
    (hm : m ∈ legalMoves (kqkPos wk wq bk .black h)) (hd : m.dst = wq) :
    KKInv (play (kqkPos wk wq bk .black h) m) := by
  obtain ⟨hm', ha, -, -, hchk⟩ := legal_kqk_black hadj hm
  obtain ⟨src, t, pr⟩ := m
  simp only [Move.mk.injEq] at hm'
  obtain ⟨h₄, -, h₅⟩ := hm'
  subst src pr
  simp only at ha hd hchk ⊢
  subst t
  have hs : (kqkPos wk wq bk .black h).board (⟨bk, wq, none⟩ : Move).src =
      some ⟨(kqkPos wk wq bk .black h).turn, .king⟩ := by
    simp [kqkPos, kqkBoard, Ne.symm h₂, Ne.symm h₃]
  have hpb := play_board_kingMove hs rfl ha
  have hbd : (play (kqkPos wk wq bk .black h) ⟨bk, wq, none⟩).board = kk wk wq := by
    rw [hpb]
    funext x
    simp only [kqkPos, kqkBoard, kk]
    split_ifs <;> simp_all
  rw [hbd, inCheck_kk_black h₁] at hchk
  exact ⟨wk, wq, h₁, hbd, by rw [kingAdj_comm]; exact hchk⟩

/-- **Capturing the queen is a dead position** (K versus K). -/
theorem kqk_black_capture_dead {wk wq bk : Square} {h : Nat} (h₁ : wk ≠ wq) (h₂ : wk ≠ bk)
    (h₃ : wq ≠ bk) (hadj : kingAdj wk bk = false) {m : Move}
    (hm : m ∈ legalMoves (kqkPos wk wq bk .black h)) (hd : m.dst = wq) :
    IsDead (play (kqkPos wk wq bk .black h) m) :=
  (kqk_black_capture_kkInv h₁ h₂ h₃ hadj hm hd).isDead

/-- **A non-capturing Black move leads to a forced mate**: after a legal Black move not landing
on the queen, White forces mate within 10 moves. -/
theorem kqk_black_step_forcesMate {wk wq bk : Square} {h : Nat} (h₁ : wk ≠ wq) (h₂ : wk ≠ bk)
    (h₃ : wq ≠ bk) (hadj : kingAdj wk bk = false) {m : Move}
    (hm : m ∈ legalMoves (kqkPos wk wq bk .black h)) (hd : m.dst ≠ wq) :
    ForcesMate .white 10 (play (kqkPos wk wq bk .black h) m) := by
  obtain ⟨hm', ha, hdk, hdb, hchk⟩ := legal_kqk_black hadj hm
  obtain ⟨src, t, pr⟩ := m
  simp only [Move.mk.injEq] at hm'
  obtain ⟨rfl, -, rfl⟩ := hm'
  simp only at ha hdk hdb hd hchk ⊢
  have h2 := kingAdj_iff.1 ha
  have hplay := play_kqk_black wk wq src t h (Ne.symm h₂) (Ne.symm h₃) hdk hd hdb
    (by omega) (by omega)
  rw [hplay] at hchk ⊢
  have hc : attackedBy (kqkBoard wk wq t) .white t = false := by
    unfold inCheck at hchk
    rw [show (kqkPos wk wq t .white (h + 1)).board = kqkBoard wk wq t from rfl,
      kingSquare_kqk_black wk wq t (Ne.symm hdk) (Ne.symm hd)] at hchk
    exact hchk
  exact kqk_forcesMate wk wq t h₁ (Ne.symm hdk) (Ne.symm hd) hc (h + 1)

/-- **White forces mate unless Black can take the queen**: if Black has a legal move and no legal
move captures the queen, White forces mate within 10 moves. -/
theorem kqk_black_forcesMate {wk wq bk : Square} {h : Nat} (h₁ : wk ≠ wq) (h₂ : wk ≠ bk)
    (h₃ : wq ≠ bk) (hadj : kingAdj wk bk = false)
    (hne : legalMoves (kqkPos wk wq bk .black h) ≠ [])
    (hcap : ∀ m ∈ legalMoves (kqkPos wk wq bk .black h), m.dst ≠ wq) :
    ForcesMate .white 10 (kqkPos wk wq bk .black h) :=
  .defend 10 _ rfl hne fun m hm => kqk_black_step_forcesMate h₁ h₂ h₃ hadj hm (hcap m hm)

/-! ### The case split -/

/-- **King and queen versus king, Black to move** (note `N-05`): in a well-formed position whose
pieces are a white king on `wk`, a white queen on `wq` and a black king on `bk`, with Black to move
and no castling rights, either Black is checkmated, or stalemated, or Black has a legal move
capturing the queen that reaches a dead position (bare kings), or White forces mate within 10
moves. -/
theorem kqk_black_to_move (p : Position) (wk wq bk : Square) (h₁ : wk ≠ wq) (h₂ : wk ≠ bk)
    (h₃ : wq ≠ bk) (hb : p.board = kqkBoard wk wq bk) (ht : p.turn = .black)
    (hcr : p.castling = .none) (hw : wellFormed p = true) :
    isCheckmate p = true ∨ isStalemate p = true ∨
      (∃ m ∈ legalMoves p, m.dst = wq ∧ IsDead (play p m)) ∨ ForcesMate .white 10 p := by
  have hep := epTarget_eq_none_of_kqk hb hw
  have hnc : inCheck (kqkBoard wk wq bk) .white = false := by
    simp only [wellFormed, Bool.and_eq_true, Bool.not_eq_true'] at hw
    have := hw.1.2
    rw [ht, hb] at this
    exact this
  have hadj := kingAdj_eq_false_of_kqk h₂ h₃ hnc
  obtain ⟨h, rfl⟩ : ∃ h, p = kqkPos wk wq bk .black h :=
    ⟨p.halfmove, by cases p; simp_all [kqkPos]⟩
  by_cases hne : legalMoves (kqkPos wk wq bk .black h) = []
  · by_cases hck : inCheck (kqkBoard wk wq bk) .black = true
    · left
      simp only [isCheckmate, hne, List.isEmpty_nil, Bool.and_true]
      exact hck
    · right; left
      simp only [Bool.not_eq_true] at hck
      simp only [isStalemate, hne, List.isEmpty_nil, Bool.and_true]
      change (!inCheck (kqkBoard wk wq bk) .black) = true
      rw [hck]; rfl
  · right; right
    by_cases hcap : ∃ m ∈ legalMoves (kqkPos wk wq bk .black h), m.dst = wq
    · left
      obtain ⟨m, hm, hd⟩ := hcap
      exact ⟨m, hm, hd, kqk_black_capture_dead h₁ h₂ h₃ hadj hm hd⟩
    · right
      simp only [not_exists, not_and] at hcap
      exact kqk_black_forcesMate h₁ h₂ h₃ hadj hne hcap

/-! ### Fixtures -/

/-- Black king h8, White king g6, White queen g7 (defended); Black to move: checkmate. -/
def kqkBlackMated : Position := kqkPos (sq 6 6) (sq 6 7) (sq 7 8) .black 0

/-- The mated fixture is well formed and checkmate (first case of `kqk_black_to_move`). -/
theorem kqkBlackMated_checkmate :
    wellFormed kqkBlackMated = true ∧ isCheckmate kqkBlackMated = true := by kernel_fact

/-- Black king a8, White king b6, White queen c7; Black to move: stalemate. -/
def kqkBlackStalemate : Position := kqkPos (sq 1 6) (sq 2 7) (sq 0 8) .black 0

/-- The stalemate fixture is well formed and stalemate (second case). -/
theorem kqkBlackStalemate_stalemate :
    wellFormed kqkBlackStalemate = true ∧ isStalemate kqkBlackStalemate = true := by kernel_fact

/-- Black king e8, White king e1, White queen e7 (undefended, giving check); Black to move. -/
def kqkBlackCapture : Position := kqkPos (sq 4 1) (sq 4 7) (sq 4 8) .black 0

/-- In the capture fixture `Kxe7` is legal and reaches a dead position (third case). -/
theorem kqkBlackCapture_dead :
    ∃ m ∈ legalMoves kqkBlackCapture, m.dst = sq 4 7 ∧ IsDead (play kqkBlackCapture m) := by
  have hm : (⟨sq 4 8, sq 4 7, none⟩ : Move) ∈ legalMoves kqkBlackCapture :=
    (isLegal_iff _ _).1 (by kernel_fact)
  have hadj : kingAdj (sq 4 1) (sq 4 8) = false := by kernel_fact
  have d₁ : sq 4 1 ≠ sq 4 7 := by simp [sq]
  have d₂ : sq 4 1 ≠ sq 4 8 := by simp [sq]
  have d₃ : sq 4 7 ≠ sq 4 8 := by simp [sq]
  exact ⟨_, hm, rfl, kqk_black_capture_dead d₁ d₂ d₃ hadj hm rfl⟩

/-- Black king e8, White king e1, White queen a1; Black to move. -/
def kqkBlackForced : Position := kqkPos (sq 4 1) (sq 0 1) (sq 4 8) .black 0

/-- In the last fixture Black has legal moves, none captures the queen, and White forces mate
within 10 moves (fourth case). -/
theorem kqkBlackForced_forcesMate : ForcesMate .white 10 kqkBlackForced := by
  have hne : legalMoves kqkBlackForced ≠ [] := by
    intro h
    have : (⟨sq 4 8, sq 3 8, none⟩ : Move) ∈ legalMoves kqkBlackForced :=
      (isLegal_iff _ _).1 (by kernel_fact)
    rw [h] at this
    simp at this
  have hcap' : (legalMoves kqkBlackForced).all (fun m => m.dst != sq 0 1) = true := by
    kernel_fact
  have hcap : ∀ m ∈ legalMoves kqkBlackForced, m.dst ≠ sq 0 1 := by
    simpa only [List.all_eq_true, bne_iff_ne] using hcap'
  have d₁ : sq 4 1 ≠ sq 0 1 := by simp [sq]
  have d₂ : sq 4 1 ≠ sq 4 8 := by simp [sq]
  have d₃ : sq 0 1 ≠ sq 4 8 := by simp [sq]
  exact kqk_black_forcesMate d₁ d₂ d₃ (by kernel_fact) hne hcap

/-- Rejected fixture: a KQK position with adjacent kings is not well formed, so
`kqk_black_to_move` does not apply to it. -/
theorem kqk_adjacent_not_wellFormed :
    wellFormed (kqkPos (sq 4 7) (sq 0 1) (sq 4 8) .black 0) = false := by kernel_fact

end LeanTheory.Chess
