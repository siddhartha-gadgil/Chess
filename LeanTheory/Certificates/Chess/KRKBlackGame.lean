/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Certificates.Chess.KRKBridge
public import LeanTheory.Certificates.Chess.KQKGame
public import LeanTheory.Certificates.Chess.KQKBlack

/-!
# King and rook versus king: Black to move, and the full game

The rook analogues (note `N-10`) of `KQKBlack` and `KQKGame`, stated for an arbitrary table
`T : Nat → Nat` all of whose entries pass `krkStateOK` and `krkCoverOK` (hypothesis `hT`). Once
the kernel check of the KRK table is complete, they apply to `krkTable` via `krkTable_ok`.

* `krk_black_to_move_of_table`: in every well-formed KRK position with Black to move and no
  castling rights, Black is checkmated, or stalemated, or has a legal capture of the rook reaching
  a dead position (bare kings), or White forces mate within 16 moves. Unlike KQK, an undefended
  rook next to the black king can really be captured; the argument is the same, since Black has
  only the king and its pseudo-legal moves are king steps (`mem_pseudoMoves_krk_black`).
* `krk_game_whiteWins_of_table` (and `_wellFormed`): from the start of a game in a KRK position
  with White to move, the black king not attacked and halfmove clock at most `118 = 150 - 2 · 16`,
  White forces a win in `chessGame` and its value is `whiteWins`. The rank (`krkRank`: twice the
  table depth with White to move, twice the largest reply depth plus one with Black to move)
  decreases strictly at every ply and is at most `32`, so neither fivefold repetition nor the
  75-move rule can intervene. The generic lemmas (`le_foldr_max`, `foldr_max_le`,
  `repetitions_eq_one`, `not_isDead_of_move`, `not_terminal_of_rep`) are reused from `KQKGame`.
-/

@[expose] public section

namespace LeanTheory.Chess

open LeanTheory.Games

/-! ### Kings on KRK boards -/

/-- The black king of a KRK board (distinct squares) stands exactly on `bk`. -/
theorem krkBoard_eq_black_king {wk wq bk : Square} (h₂ : wk ≠ bk) (h₃ : wq ≠ bk) (u : Square) :
    krkBoard wk wq bk u = some ⟨.black, .king⟩ ↔ u = bk := by
  unfold krkBoard; split_ifs <;> simp_all

/-- The white king of a KRK board stands exactly on `wk`. -/
theorem krkBoard_eq_white_king {wk wq bk : Square} (u : Square) :
    krkBoard wk wq bk u = some ⟨.white, .king⟩ ↔ u = wk := by
  unfold krkBoard; split_ifs <;> simp_all

/-- The white king of a KRK board is found on `wk`. -/
theorem kingSquare_krk_white (wk wq bk : Square) :
    kingSquare (krkBoard wk wq bk) .white = some wk :=
  kingSquare_unique krkBoard_eq_white_king

/-- If White is not in check on a KRK board, the kings are not adjacent. -/
theorem kingAdj_eq_false_of_krk {wk wq bk : Square} (h₂ : wk ≠ bk) (h₃ : wq ≠ bk)
    (hc : inCheck (krkBoard wk wq bk) .white = false) : kingAdj wk bk = false := by
  unfold inCheck at hc
  rw [kingSquare_krk_white] at hc
  simp only [Color.other] at hc
  unfold attackedBy at hc
  rw [pieceAtOffsets_unique (krkBoard_eq_black_king h₂ h₃)] at hc
  simp only [Bool.or_eq_false_iff] at hc
  exact hc.1.1.1.2

/-! ### Black's moves -/

/-- On a KRK board with Black to move, every pseudo-legal move is a plain step of the black
king. -/
theorem mem_pseudoMoves_krk_black {wk wq bk : Square} {h : Nat} {m : Move}
    (hm : m ∈ pseudoMoves (krkPos wk wq bk .black h)) :
    m.src = bk ∧ m.promo = none ∧ kingAdj bk m.dst = true := by
  have hr : castlingMoves (krkPos wk wq bk .black h) = [] := by
    simp [castlingMoves, krkPos, CastlingRights.kingSide, CastlingRights.queenSide,
      CastlingRights.none]
  simp only [pseudoMoves, hr, List.append_nil, List.mem_flatMap] at hm
  obtain ⟨s, -, hm⟩ := hm
  split at hm
  · rename_i pc hs
    split_ifs at hm with hc
    · obtain ⟨c, k⟩ := pc
      simp only [krkPos] at hc hs
      subst hc
      have hk : k = .king ∧ s = bk := by
        unfold krkBoard at hs; split_ifs at hs <;> simp_all
      obtain ⟨rfl, rfl⟩ := hk
      simp only [pieceMoves, List.mem_map] at hm
      obtain ⟨t, ht, rfl⟩ := hm
      obtain ⟨⟨d, hd, hu⟩, -⟩ := mem_stepTargets.1 ht
      refine ⟨rfl, rfl, ?_⟩
      simp only [kingAdj, List.any_eq_true, beq_iff_eq]
      exact ⟨d, hd, hu⟩
    · simp at hm
  · simp at hm

/-- A legal Black move in a KRK position with non-adjacent kings is the king step
`⟨bk, t, none⟩` to a square `t ≠ wk, bk` adjacent to `bk`, after which Black is not in check. -/
theorem legal_krk_black {wk wq bk : Square} {h : Nat} (hadj : kingAdj wk bk = false) {m : Move}
    (hm : m ∈ legalMoves (krkPos wk wq bk .black h)) :
    m = ⟨bk, m.dst, none⟩ ∧ kingAdj bk m.dst = true ∧ m.dst ≠ wk ∧ m.dst ≠ bk ∧
      inCheck (play (krkPos wk wq bk .black h) m).board .black = false := by
  simp only [legalMoves, List.mem_filter, Bool.not_eq_true'] at hm
  obtain ⟨hps, hchk⟩ := hm
  obtain ⟨hs, hp, ha⟩ := mem_pseudoMoves_krk_black hps
  refine ⟨by cases m; simp_all, ha, ?_, (kingAdj_iff.1 ha).1.symm, hchk⟩
  rintro hd
  rw [hd, kingAdj_comm, hadj] at ha
  exact Bool.false_ne_true ha

/-- **Capturing the rook gives bare kings**: if Black's legal move captures the rook on a KRK
board with non-adjacent kings, the result has two non-adjacent bare kings (`KKInv`). -/
theorem krk_black_capture_kkInv {wk wq bk : Square} {h : Nat} (h₁ : wk ≠ wq) (h₂ : wk ≠ bk)
    (h₃ : wq ≠ bk) (hadj : kingAdj wk bk = false) {m : Move}
    (hm : m ∈ legalMoves (krkPos wk wq bk .black h)) (hd : m.dst = wq) :
    KKInv (play (krkPos wk wq bk .black h) m) := by
  obtain ⟨hm', ha, -, -, hchk⟩ := legal_krk_black hadj hm
  obtain ⟨src, t, pr⟩ := m
  simp only [Move.mk.injEq] at hm'
  obtain ⟨h₄, -, h₅⟩ := hm'
  subst src pr
  simp only at ha hd hchk ⊢
  subst t
  have hs : (krkPos wk wq bk .black h).board (⟨bk, wq, none⟩ : Move).src =
      some ⟨(krkPos wk wq bk .black h).turn, .king⟩ := by
    simp [krkPos, krkBoard, Ne.symm h₂, Ne.symm h₃]
  have hpb := play_board_kingMove hs rfl ha
  have hbd : (play (krkPos wk wq bk .black h) ⟨bk, wq, none⟩).board = kk wk wq := by
    rw [hpb]
    funext x
    simp only [krkPos, krkBoard, kk]
    split_ifs <;> simp_all
  rw [hbd, inCheck_kk_black h₁] at hchk
  exact ⟨wk, wq, h₁, hbd, by rw [kingAdj_comm]; exact hchk⟩

/-- **Capturing the rook is a dead position** (K versus K). -/
theorem krk_black_capture_dead {wk wq bk : Square} {h : Nat} (h₁ : wk ≠ wq) (h₂ : wk ≠ bk)
    (h₃ : wq ≠ bk) (hadj : kingAdj wk bk = false) {m : Move}
    (hm : m ∈ legalMoves (krkPos wk wq bk .black h)) (hd : m.dst = wq) :
    IsDead (play (krkPos wk wq bk .black h) m) :=
  (krk_black_capture_kkInv h₁ h₂ h₃ hadj hm hd).isDead

/-- **A non-capturing Black move leads to a forced mate** (given a checked table): after a legal
Black move not landing on the rook, White forces mate within 16 moves. -/
theorem krk_black_step_forcesMate_of_table (T : Nat → Nat)
    (hT : ∀ i, i < 262144 → krkStateOK T i = true ∧ krkCoverOK T i = true)
    {wk wq bk : Square} {h : Nat} (h₁ : wk ≠ wq) (h₂ : wk ≠ bk)
    (h₃ : wq ≠ bk) (hadj : kingAdj wk bk = false) {m : Move}
    (hm : m ∈ legalMoves (krkPos wk wq bk .black h)) (hd : m.dst ≠ wq) :
    ForcesMate .white 16 (play (krkPos wk wq bk .black h) m) := by
  obtain ⟨hm', ha, hdk, hdb, hchk⟩ := legal_krk_black hadj hm
  obtain ⟨src, t, pr⟩ := m
  simp only [Move.mk.injEq] at hm'
  obtain ⟨rfl, -, rfl⟩ := hm'
  simp only at ha hdk hdb hd hchk ⊢
  have h2 := kingAdj_iff.1 ha
  have hplay := play_krk_black wk wq src t h (Ne.symm h₂) (Ne.symm h₃) hdk hd hdb
    (by omega) (by omega)
  rw [hplay] at hchk ⊢
  have hc : attackedBy (krkBoard wk wq t) .white t = false := by
    unfold inCheck at hchk
    rw [show (krkPos wk wq t .white (h + 1)).board = krkBoard wk wq t from rfl,
      kingSquare_krk_black wk wq t (Ne.symm hdk) (Ne.symm hd)] at hchk
    exact hchk
  exact krk_forcesMate_of_table T hT wk wq t h₁ (Ne.symm hdk) (Ne.symm hd) hc (h + 1)

/-- **White forces mate unless Black can take the rook** (given a checked table): if Black has a
legal move and no legal move captures the rook, White forces mate within 16 moves. -/
theorem krk_black_forcesMate_of_table (T : Nat → Nat)
    (hT : ∀ i, i < 262144 → krkStateOK T i = true ∧ krkCoverOK T i = true)
    {wk wq bk : Square} {h : Nat} (h₁ : wk ≠ wq) (h₂ : wk ≠ bk)
    (h₃ : wq ≠ bk) (hadj : kingAdj wk bk = false)
    (hne : legalMoves (krkPos wk wq bk .black h) ≠ [])
    (hcap : ∀ m ∈ legalMoves (krkPos wk wq bk .black h), m.dst ≠ wq) :
    ForcesMate .white 16 (krkPos wk wq bk .black h) :=
  .defend 16 _ rfl hne fun m hm =>
    krk_black_step_forcesMate_of_table T hT h₁ h₂ h₃ hadj hm (hcap m hm)

/-! ### The Black-to-move case split -/

/-- **King and rook versus king, Black to move** (note `N-10`, given a checked table `T`): in a
well-formed position whose pieces are a white king on `wk`, a white rook on `wq` and a black king
on `bk`, with Black to move and no castling rights, either Black is checkmated, or stalemated, or
Black has a legal move capturing the rook that reaches a dead position (bare kings), or White
forces mate within 16 moves. -/
theorem krk_black_to_move_of_table (T : Nat → Nat)
    (hT : ∀ i, i < 262144 → krkStateOK T i = true ∧ krkCoverOK T i = true)
    (p : Position) (wk wq bk : Square) (h₁ : wk ≠ wq) (h₂ : wk ≠ bk)
    (h₃ : wq ≠ bk) (hb : p.board = krkBoard wk wq bk) (ht : p.turn = .black)
    (hcr : p.castling = .none) (hw : wellFormed p = true) :
    isCheckmate p = true ∨ isStalemate p = true ∨
      (∃ m ∈ legalMoves p, m.dst = wq ∧ IsDead (play p m)) ∨ ForcesMate .white 16 p := by
  have hep := epTarget_eq_none_of_krk hb hw
  have hnc : inCheck (krkBoard wk wq bk) .white = false := by
    simp only [wellFormed, Bool.and_eq_true, Bool.not_eq_true'] at hw
    have := hw.1.2
    rw [ht, hb] at this
    exact this
  have hadj := kingAdj_eq_false_of_krk h₂ h₃ hnc
  obtain ⟨h, rfl⟩ : ∃ h, p = krkPos wk wq bk .black h :=
    ⟨p.halfmove, by cases p; simp_all [krkPos]⟩
  by_cases hne : legalMoves (krkPos wk wq bk .black h) = []
  · by_cases hck : inCheck (krkBoard wk wq bk) .black = true
    · left
      simp only [isCheckmate, hne, List.isEmpty_nil, Bool.and_true]
      exact hck
    · right; left
      simp only [Bool.not_eq_true] at hck
      simp only [isStalemate, hne, List.isEmpty_nil, Bool.and_true]
      change (!inCheck (krkBoard wk wq bk) .black) = true
      rw [hck]; rfl
  · right; right
    by_cases hcap : ∃ m ∈ legalMoves (krkPos wk wq bk .black h), m.dst = wq
    · left
      obtain ⟨m, hm, hd⟩ := hcap
      exact ⟨m, hm, hd, krk_black_capture_dead h₁ h₂ h₃ hadj hm hd⟩
    · right
      simp only [not_exists, not_and] at hcap
      exact krk_black_forcesMate_of_table T hT h₁ h₂ h₃ hadj hne hcap

/-! ### Ranks -/

/-- The table depth of the White-to-move KRK triple `(a, b, c)`. -/
def krkWDepth (T : Nat → Nat) (a b c : Square) : Nat := krkDepth (T (kqkIdx a.val b.val c.val))

/-- The largest table depth among the positions reached by Black's legal replies (`0` if none). -/
def krkMaxReplyDepth (T : Nat → Nat) (a b c : Square) : Nat :=
  ((legalMoves (krkPos a b c .black 0)).map fun m => krkWDepth T a b m.dst).foldr max 0

/-- The rank of a KRK position: `2 · depth` with White to move, `2 · krkMaxReplyDepth + 1` with
Black to move. -/
def krkRank (T : Nat → Nat) (a b c : Square) : Color → Nat
  | .white => 2 * krkWDepth T a b c
  | .black => 2 * krkMaxReplyDepth T a b c + 1

/-! ### One step of the certified strategy -/

/-- **White's step**: from a White-to-move triple with nonzero depth, the table move is legal and
leads to a Black-to-move KRK position accepted by `krkAfterWhiteOK` at that depth. -/
theorem krk_white_step (T : Nat → Nat) (hT : ∀ i, i < 262144 → krkStateOK T i = true)
    (a b c : Square) (h₁ : a ≠ b) (h₂ : a ≠ c) (h₃ : b ≠ c)
    (hd : krkWDepth T a b c ≠ 0) (h : Nat) :
    ∃ m ∈ legalMoves (krkPos a b c .white h), ∃ a' b' : Square, a' ≠ b' ∧ c ≠ a' ∧ c ≠ b' ∧
      play (krkPos a b c .white h) m = krkPos a' b' c .black (h + 1) ∧
      krkAfterWhiteOK T (krkWDepth T a b c) a' b' c = true := by
  have hi : kqkIdx a.val b.val c.val < 262144 := by
    have := a.isLt; have := b.isLt; have := c.isLt; simp only [kqkIdx]; omega
  have hs := hT _ hi
  obtain ⟨e₁, e₂, e₃⟩ := sqOf_kqkIdx a b c
  unfold krkWDepth at hd ⊢
  simp only [krkStateOK, e₁, e₂, e₃, Bool.or_eq_true, beq_iff_eq, hd, false_or,
    Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hs
  obtain ⟨_, hw⟩ := hs
  generalize sqOf (krkSrc (T (kqkIdx a.val b.val c.val))) = src at hw
  generalize sqOf (krkDst (T (kqkIdx a.val b.val c.val))) = dst at hw
  simp only [krkWhiteOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    List.contains_iff_mem] at hw
  rcases hw with ⟨⟨⟨⟨⟨⟨⟨_, hd₀⟩, hd₁⟩, hd₂⟩, hd₃⟩, hd₄⟩, hmem⟩, hok⟩ |
      ⟨⟨⟨⟨⟨_, hd₀⟩, hd₁⟩, hd₂⟩, hmem⟩, hok⟩
  · have hplay := play_krk_king a b c dst h h₁ h₂ hd₀ hd₁ hd₂ hd₃ hd₄
    have hc : inCheck (krkBoard dst b c) .white = false := by
      have := hok
      simp only [krkAfterWhiteOK, Bool.and_eq_true, Bool.not_eq_true'] at this
      exact this.1
    refine ⟨⟨a, dst, none⟩, mem_legalMoves_of _ a .king _ (by simp [krkPos, krkBoard]) hmem
      (by rw [hplay]; exact hc), dst, b, hd₁, Ne.symm hd₂, Ne.symm h₃, hplay, hok⟩
  · have hplay := play_krk_rook a b c dst h h₁ h₃ hd₀ hd₁ hd₂
    have hc : inCheck (krkBoard a dst c) .white = false := by
      have := hok
      simp only [krkAfterWhiteOK, Bool.and_eq_true, Bool.not_eq_true'] at this
      exact this.1
    refine ⟨⟨b, dst, none⟩, mem_legalMoves_of _ b .rook _
      (by simp [krkPos, krkBoard, Ne.symm h₁]) hmem (by rw [hplay]; exact hc), a, dst,
      Ne.symm hd₀, Ne.symm h₂, Ne.symm hd₂, hplay, hok⟩

/-- **Black's position after White's step**: either Black is checkmated, or Black has legal moves,
each a non-capturing king step to a White-to-move triple of depth in `(0, d)`. -/
theorem krk_black_cases (T : Nat → Nat) (a b c : Square) (d : Nat) (hca : c ≠ a) (hcb : c ≠ b)
    (hok : krkAfterWhiteOK T d a b c = true) (h : Nat) :
    isCheckmate (krkPos a b c .black h) = true ∨
      (legalMoves (krkPos a b c .black h) ≠ [] ∧ ∀ m ∈ legalMoves (krkPos a b c .black h),
        m.dst ≠ a ∧ m.dst ≠ b ∧
          play (krkPos a b c .black h) m = krkPos a b m.dst .white (h + 1) ∧
          0 < krkWDepth T a b m.dst ∧ krkWDepth T a b m.dst < d) := by
  simp only [krkAfterWhiteOK, Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨_, hok⟩ := hok
  have hlm : legalMoves (krkPos a b c .black h) = legalMoves (krkPos a b c .black 0) := rfl
  split at hok
  · rename_i hnil
    left
    simp only [isCheckmate, hlm, hnil, List.isEmpty_nil, Bool.and_true]
    exact hok
  · rename_i m₀ ms hcons
    right
    refine ⟨by rw [hlm, hcons]; simp, fun m hm => ?_⟩
    have hr := List.all_eq_true.1 hok m (by rw [← hcons, ← hlm]; exact hm)
    simp only [krkReplyOK, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hr
    obtain ⟨⟨⟨⟨⟨⟨⟨hsrc, hpro⟩, hd₀⟩, hd₁⟩, hd₂⟩, hd₃⟩, hd₄⟩, hpos, hlt⟩ := hr
    have hm' : m = ⟨c, m.dst, none⟩ := by cases m; simp_all
    refine ⟨hd₀, hd₁, ?_, hpos, hlt⟩
    rw [hm']
    exact play_krk_black a b c m.dst h hca hcb hd₀ hd₁ hd₂ hd₃ hd₄

/-! ### Positions on the lines and repetition -/

/-- A KRK board with distinct squares equals another KRK board only for the same squares. -/
theorem krkBoard_inj {a b c a' b' c' : Square} (h₁ : a ≠ b) (h₂ : a ≠ c) (h₃ : b ≠ c)
    (H : krkBoard a b c = krkBoard a' b' c') : a = a' ∧ b = b' ∧ c = c' := by
  have ea : krkBoard a' b' c' a = some ⟨.white, .king⟩ := by rw [← H]; simp [krkBoard]
  have eb : krkBoard a' b' c' b = some ⟨.white, .rook⟩ := by
    rw [← H]; simp [krkBoard, Ne.symm h₁]
  have ec : krkBoard a' b' c' c = some ⟨.black, .king⟩ := by
    rw [← H]; simp [krkBoard, Ne.symm h₂, Ne.symm h₃]
  clear H
  unfold krkBoard at ea eb ec
  refine ⟨?_, ?_, ?_⟩
  · split_ifs at ea <;> first | assumption | simp at ea
  · split_ifs at eb <;> first | assumption | simp at eb
  · split_ifs at ec <;> first | assumption | simp at ec

/-- A node of a line: a KRK position given by its squares, side to move and clock. -/
structure KRKNode where
  /-- White king. -/
  a : Square
  /-- White rook. -/
  b : Square
  /-- Black king. -/
  c : Square
  /-- Side to move. -/
  t : Color
  /-- Halfmove clock. -/
  h : Nat

/-- The position of a node. -/
def KRKNode.pos (e : KRKNode) : Position := krkPos e.a e.b e.c e.t e.h

/-- The rank of a node for the table `T`. -/
def KRKNode.rank (T : Nat → Nat) (e : KRKNode) : Nat := krkRank T e.a e.b e.c e.t

/-- The three squares of a node are distinct. -/
def KRKNode.Distinct (e : KRKNode) : Prop := e.a ≠ e.b ∧ e.a ≠ e.c ∧ e.b ≠ e.c

/-- Nodes in the same position (FIDE 9.2.3) have the same rank. -/
theorem KRKNode.rank_eq_of_same (T : Nat → Nat) {e e' : KRKNode} (hd : e.Distinct)
    (hs : samePosition e.pos e'.pos = true) : e.rank T = e'.rank T := by
  rw [samePosition_iff] at hs
  simp only [key, KRKNode.pos, krkPos, Prod.mk.injEq] at hs
  obtain ⟨ht, hb, _⟩ := hs
  obtain ⟨ha, hb', hc⟩ := krkBoard_inj hd.1 hd.2.1 hd.2.2 hb
  simp only [KRKNode.rank, ha, hb', hc, ht]

/-! ### The induction along the lines -/

/-- The node is on a line of the strategy for `T`: with White to move its depth is nonzero; with
Black to move it was reached by a White step accepted at some depth `d ≥ 1` (`krkAfterWhiteOK`),
and its rank is below `2 d`. -/
def KRKNode.OK (T : Nat → Nat) (e : KRKNode) : Prop :=
  match e.t with
  | .white => krkWDepth T e.a e.b e.c ≠ 0
  | .black => ∃ d, 1 ≤ d ∧ krkAfterWhiteOK T d e.a e.b e.c = true ∧
      2 * krkMaxReplyDepth T e.a e.b e.c + 1 ≤ 2 * d - 1

/-- **White wins along the certified lines** (given a checked table): from a game state whose
current position is a node on a line and whose earlier positions are nodes of larger rank, with
clock plus rank at most 150, White guarantees a win in `chessGame`. -/
theorem krk_guarantees_of_node (T : Nat → Nat) (hT : ∀ i, i < 262144 → krkStateOK T i = true) :
    ∀ r (cur : KRKNode) (hist : List KRKNode) (s : State),
    s.1 = ⟨cur.pos, hist.map KRKNode.pos⟩ → cur.Distinct → cur.OK T → cur.rank T = r →
    cur.h + r ≤ 150 → (∀ e ∈ hist, r < e.rank T) →
    chessGame.GuaranteesGe .whiteWins s := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro cur hist s hs hdist hok hr hh hhist
  have hrep : s.1.repetitions = 1 := by
    apply repetitions_eq_one
    rw [hs]
    intro q hq
    simp only [List.mem_map] at hq
    obtain ⟨e, he, rfl⟩ := hq
    cases hsp : samePosition cur.pos e.pos
    · rfl
    · have := KRKNode.rank_eq_of_same T hdist hsp
      have := hhist e he
      omega
  obtain ⟨a, b, c, t, h⟩ := cur
  obtain ⟨h₁, h₂, h₃⟩ := hdist
  dsimp only at h₁ h₂ h₃ hh
  cases t with
  | white =>
    simp only [KRKNode.OK] at hok
    simp only [KRKNode.rank, krkRank] at hr
    obtain ⟨m, hm, a', b', h₁', hca, hcb, hplay, hafter⟩ :=
      krk_white_step T hT a b c h₁ h₂ h₃ hok h
    have hfm := krk_table_sound T hT _ a b c rfl hok h
    have hpos : s.1.pos = krkPos a b c .white h := by rw [hs]; rfl
    have hlt : s.1.pos.halfmove < 150 := by rw [hpos]; simp only [krkPos]; omega
    have hnt : ¬ s.1.IsTerminal :=
      not_terminal_of_rep (m := m) (by rw [hpos]; exact hm) hlt hrep
        (by rw [hpos]; exact hfm.not_isDead)
    let t : State := ⟨s.1.play m, valid_play s.2 hnt m⟩
    refine Game.GuaranteesGe.first s t (by simp [chessGame, colorPlayer, hpos, krkPos])
      (mem_chessMoves.2 ⟨hnt, m, by rw [hpos]; exact hm, rfl⟩) ?_
    -- the Black node
    have hmax : krkMaxReplyDepth T a' b' c < krkWDepth T a b c := by
      rcases krk_black_cases T a' b' c _ hca hcb hafter 0 with hmate | ⟨_, hall⟩
      · have : legalMoves (krkPos a' b' c .black 0) = [] := by
          simp only [isCheckmate, Bool.and_eq_true, List.isEmpty_iff] at hmate
          exact hmate.2
        simp only [krkMaxReplyDepth, this, List.map_nil, List.foldr_nil]
        omega
      · have : krkMaxReplyDepth T a' b' c ≤ krkWDepth T a b c - 1 :=
          foldr_max_le fun x hx => by
            simp only [List.mem_map] at hx
            obtain ⟨m', hm', rfl⟩ := hx
            have := (hall m' hm').2.2.2
            omega
        omega
    refine ih (2 * krkMaxReplyDepth T a' b' c + 1) (by omega) ⟨a', b', c, .black, h + 1⟩
      (⟨a, b, c, .white, h⟩ :: hist) t ?_ ⟨h₁', Ne.symm hca, Ne.symm hcb⟩
      ⟨krkWDepth T a b c, by omega, hafter, by dsimp only; omega⟩ rfl (by simp only; omega) ?_
    · change s.1.play m = _
      simp only [GameState.play, hs, List.map_cons]
      rw [show (⟨a, b, c, .white, h⟩ : KRKNode).pos = krkPos a b c .white h from rfl]
      rw [show (⟨a', b', c, .black, h + 1⟩ : KRKNode).pos = krkPos a' b' c .black (h + 1)
        from rfl]
      rw [← hplay]
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · simp only [KRKNode.rank, krkRank]; omega
      · have := hhist e he; omega
  | black =>
    simp only [KRKNode.OK] at hok
    obtain ⟨d, hd1, hafter, hdr⟩ := hok
    simp only [KRKNode.rank, krkRank] at hr
    have hpos : s.1.pos = krkPos a b c .black h := by rw [hs]; rfl
    rcases krk_black_cases T a b c d (Ne.symm h₂) (Ne.symm h₃) hafter h with hmate | ⟨hne, hall⟩
    · refine Game.GuaranteesGe.terminal s ?_ ?_
      · exact (chessMoves_eq_nil_iff s).2 (Or.inl (by rw [hpos]; exact hmate))
      · have hm' := hmate
        simp only [krkPos] at hm'
        simp [chessGame, chessOutcome, hpos, hm', krkPos, matedOutcome]
    · obtain ⟨m₀, hm₀⟩ := List.exists_mem_of_ne_nil _ hne
      obtain ⟨_, _, hp₀, hpos₀, _⟩ := hall m₀ hm₀
      have hfm := krk_table_sound T hT _ a b m₀.dst rfl (Nat.pos_iff_ne_zero.mp hpos₀) (h + 1)
      have hlt : s.1.pos.halfmove < 150 := by rw [hpos]; simp only [krkPos]; omega
      have hnt : ¬ s.1.IsTerminal := by
        refine not_terminal_of_rep (m := m₀) (by rw [hpos]; exact hm₀) hlt hrep ?_
        rw [hpos]
        exact not_isDead_of_move hm₀ (by rw [hp₀]; exact hfm.not_isDead)
      refine Game.GuaranteesGe.second s
        (fun h0 => hnt ((chessMoves_eq_nil_iff s).1 h0))
        (by simp [chessGame, colorPlayer, hpos, krkPos]) fun u hu => ?_
      obtain ⟨_, m, hm, hu⟩ := mem_chessMoves.1 hu
      rw [hpos] at hm
      obtain ⟨hda, hdb, hp, hpos', hlt⟩ := hall m hm
      have hle : krkWDepth T a b m.dst ≤ krkMaxReplyDepth T a b c :=
        le_foldr_max (List.mem_map.2 ⟨m, hm, rfl⟩)
      refine ih (2 * krkWDepth T a b m.dst) (by omega) ⟨a, b, m.dst, .white, h + 1⟩
        (⟨a, b, c, .black, h⟩ :: hist) u ?_ ⟨h₁, Ne.symm hda, Ne.symm hdb⟩
        (by dsimp only [KRKNode.OK]; omega) rfl (by simp only; omega) ?_
      · rw [hu]
        simp only [GameState.play, hs, List.map_cons]
        rw [show (⟨a, b, c, .black, h⟩ : KRKNode).pos = krkPos a b c .black h from rfl]
        rw [show (⟨a, b, m.dst, .white, h + 1⟩ : KRKNode).pos =
          krkPos a b m.dst .white (h + 1) from rfl]
        rw [← hp]
      · intro e he
        rcases List.mem_cons.1 he with rfl | he
        · simp only [KRKNode.rank, krkRank]; omega
        · have := hhist e he; omega

/-! ### Main theorems -/

/-- **King and rook versus king in the full game** (rule model `A`, given a checked table `T`):
from the start of a game in a KRK position with White to move, the black king not attacked and
halfmove clock at most 118 (`= 150 - 2 · 16`), White can force a win, and the value of the game
is `whiteWins`. -/
theorem krk_game_whiteWins_of_table (T : Nat → Nat)
    (hT : ∀ i, i < 262144 → krkStateOK T i = true ∧ krkCoverOK T i = true)
    (a b c : Square) (h₁ : a ≠ b) (h₂ : a ≠ c) (h₃ : b ≠ c)
    (hc : attackedBy (krkBoard a b c) .white c = false) (h : Nat) (hh : h ≤ 118) :
    chessGame.MaxForces .whiteWins (State.start (krkPos a b c .white h)) ∧
      chessGame.value (State.start (krkPos a b c .white h)) = .whiteWins := by
  have hi : kqkIdx a.val b.val c.val < 262144 := by
    have := a.isLt; have := b.isLt; have := c.isLt; simp only [kqkIdx]; omega
  obtain ⟨hs, hcov⟩ := hT _ hi
  obtain ⟨e₁, e₂, e₃⟩ := sqOf_kqkIdx a b c
  simp only [krkCoverOK, e₁, e₂, e₃, hc, Bool.or_eq_true, beq_iff_eq, h₁, h₂, h₃, false_or,
    bne_iff_ne, ne_eq, Bool.false_eq_true] at hcov
  have hle : krkWDepth T a b c ≤ 16 := by
    simp only [krkStateOK, Bool.or_eq_true, beq_iff_eq, hcov, false_or, Bool.and_eq_true,
      decide_eq_true_eq] at hs
    exact hs.1.1.1.1
  have hg := krk_guarantees_of_node T (fun i hi => (hT i hi).1) (2 * krkWDepth T a b c)
    ⟨a, b, c, .white, h⟩ [] (State.start (krkPos a b c .white h)) rfl ⟨h₁, h₂, h₃⟩ hcov rfl
    (by simp only; omega) (by simp)
  have hv := (chessGame.guaranteesGe_iff _ _).1 hg
  exact ⟨(chessGame.maxForces_iff _ _).2 hv, (chessGame.maxForces_whiteWins_iff _).1
    ((chessGame.maxForces_iff _ _).2 hv)⟩

/-- **King and rook versus king in the full game, for well-formed positions** (given a checked
table `T`): from the start of a game in any well-formed position whose pieces are a white king, a
white rook and a black king, with White to move, no castling rights and halfmove clock at most
118, White can force a win in `chessGame`, whose value there is `whiteWins`. -/
theorem krk_game_whiteWins_of_table_wellFormed (T : Nat → Nat)
    (hT : ∀ i, i < 262144 → krkStateOK T i = true ∧ krkCoverOK T i = true)
    (p : Position) (a b c : Square) (h₁ : a ≠ b) (h₂ : a ≠ c)
    (h₃ : b ≠ c) (hb : p.board = krkBoard a b c) (ht : p.turn = .white)
    (hcr : p.castling = .none) (hw : wellFormed p = true) (hh : p.halfmove ≤ 118) :
    chessGame.MaxForces .whiteWins (State.start p) ∧
      chessGame.value (State.start p) = .whiteWins := by
  have hep := epTarget_eq_none_of_krk hb hw
  have hc : attackedBy (krkBoard a b c) .white c = false := by
    simp only [wellFormed, Bool.and_eq_true, Bool.not_eq_true'] at hw
    have := hw.1.2
    rw [ht, hb] at this
    simpa [inCheck, Color.other, kingSquare_krk_black a b c h₂ h₃] using this
  have hp : p = krkPos a b c .white p.halfmove := by
    cases p; simp_all [krkPos]
  rw [hp]
  exact krk_game_whiteWins_of_table T hT a b c h₁ h₂ h₃ hc p.halfmove hh

end LeanTheory.Chess
