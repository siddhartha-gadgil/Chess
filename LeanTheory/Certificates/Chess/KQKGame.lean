/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Certificates.Chess.KQK
public import LeanTheory.Theory.Chess.Determinacy

/-!
# King and queen versus king in the full game with draw rules

`Certificates/Chess/KQK` proves `ForcesMate` for KQK positions; `ForcesMate` ignores the draw
rules that depend on the game record. This file (note `N-05`) proves the statement for the game
`chessGame` of `Theory/Chess/Determinacy` (rule model `A`: checkmate, stalemate, dead position,
fivefold repetition, 75-move rule): from the start of a game in a KQK position with White to move,
the black king not attacked and halfmove clock at most 130, **White forces a win and the game
value is `whiteWins`** (`kqk_game_whiteWins`, `kqk_game_whiteWins_wellFormed`).

Method: White follows the certified table. Each position on the resulting lines gets a rank
(`kqkRank`: twice the table depth with White to move, twice the largest depth of a Black reply plus
one with Black to move) that strictly decreases at every ply. Hence no position repeats
(`samePosition` forces equal squares, side to move and rank), the fivefold rule never applies, and
since the rank is at most 20 the 75-move rule does not apply when the clock starts at most 130.
Dead positions are excluded by `ForcesMate.not_isDead`.
-/

@[expose] public section

namespace LeanTheory.Chess

open LeanTheory.Games

/-! ### Ranks -/

/-- The table depth of the White-to-move KQK triple `(a, b, c)`. -/
def wDepth (a b c : Square) : Nat := entDepth (kqkTable (kqkIdx a.val b.val c.val))

/-- The largest table depth among the positions reached by Black's legal replies (`0` if none). -/
def maxReplyDepth (a b c : Square) : Nat :=
  ((legalMoves (kqkPos a b c .black 0)).map fun m => wDepth a b m.dst).foldr max 0

/-- The rank of a KQK position: `2 · depth` with White to move, `2 · maxReplyDepth + 1` with Black
to move. -/
def kqkRank (a b c : Square) : Color → Nat
  | .white => 2 * wDepth a b c
  | .black => 2 * maxReplyDepth a b c + 1

/-- An element of a list is at most its `foldr max 0`. -/
theorem le_foldr_max {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

/-- `foldr max 0` is at most any common upper bound. -/
theorem foldr_max_le {l : List Nat} {k : Nat} (h : ∀ x ∈ l, x ≤ k) : l.foldr max 0 ≤ k := by
  induction l with
  | nil => simp
  | cons y l ih =>
    simp only [List.foldr_cons]
    exact max_le (h y (by simp)) (ih fun x hx => h x (by simp [hx]))

/-! ### One step of the certified strategy -/

/-- **White's step**: from a White-to-move triple with nonzero depth, the table move is legal and
leads to a Black-to-move KQK position accepted by `afterWhiteOK` at that depth. -/
theorem white_step (a b c : Square) (h₁ : a ≠ b) (h₂ : a ≠ c) (h₃ : b ≠ c)
    (hd : wDepth a b c ≠ 0) (h : Nat) :
    ∃ m ∈ legalMoves (kqkPos a b c .white h), ∃ a' b' : Square, a' ≠ b' ∧ c ≠ a' ∧ c ≠ b' ∧
      play (kqkPos a b c .white h) m = kqkPos a' b' c .black (h + 1) ∧
      afterWhiteOK kqkTable (wDepth a b c) a' b' c = true := by
  have hi : kqkIdx a.val b.val c.val < 262144 := by
    have := a.isLt; have := b.isLt; have := c.isLt; simp only [kqkIdx]; omega
  have hs := (kqkTable_ok _ hi).1
  obtain ⟨e₁, e₂, e₃⟩ := sqOf_kqkIdx a b c
  unfold wDepth at hd ⊢
  simp only [stateOK, e₁, e₂, e₃, Bool.or_eq_true, beq_iff_eq, hd, false_or,
    Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hs
  obtain ⟨_, hw⟩ := hs
  generalize sqOf (entSrc (kqkTable (kqkIdx a.val b.val c.val))) = src at hw
  generalize sqOf (entDst (kqkTable (kqkIdx a.val b.val c.val))) = dst at hw
  simp only [whiteOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    List.contains_iff_mem] at hw
  rcases hw with ⟨⟨⟨⟨⟨⟨⟨_, hd₀⟩, hd₁⟩, hd₂⟩, hd₃⟩, hd₄⟩, hmem⟩, hok⟩ |
      ⟨⟨⟨⟨⟨_, hd₀⟩, hd₁⟩, hd₂⟩, hmem⟩, hok⟩
  · have hplay := play_kqk_king a b c dst h h₁ h₂ hd₀ hd₁ hd₂ hd₃ hd₄
    have hc : inCheck (kqkBoard dst b c) .white = false := by
      have := hok
      simp only [afterWhiteOK, Bool.and_eq_true, Bool.not_eq_true'] at this
      exact this.1
    refine ⟨⟨a, dst, none⟩, mem_legalMoves_of _ a .king _ (by simp [kqkPos, kqkBoard]) hmem
      (by rw [hplay]; exact hc), dst, b, hd₁, Ne.symm hd₂, Ne.symm h₃, hplay, hok⟩
  · have hplay := play_kqk_queen a b c dst h h₁ h₃ hd₀ hd₁ hd₂
    have hc : inCheck (kqkBoard a dst c) .white = false := by
      have := hok
      simp only [afterWhiteOK, Bool.and_eq_true, Bool.not_eq_true'] at this
      exact this.1
    refine ⟨⟨b, dst, none⟩, mem_legalMoves_of _ b .queen _
      (by simp [kqkPos, kqkBoard, Ne.symm h₁]) hmem (by rw [hplay]; exact hc), a, dst,
      Ne.symm hd₀, Ne.symm h₂, Ne.symm hd₂, hplay, hok⟩

/-- **Black's position after White's step**: either Black is checkmated, or Black has legal moves,
each a non-capturing king step to a White-to-move triple of depth in `(0, d)`. -/
theorem black_cases (a b c : Square) (d : Nat) (hca : c ≠ a) (hcb : c ≠ b)
    (hok : afterWhiteOK kqkTable d a b c = true) (h : Nat) :
    isCheckmate (kqkPos a b c .black h) = true ∨
      (legalMoves (kqkPos a b c .black h) ≠ [] ∧ ∀ m ∈ legalMoves (kqkPos a b c .black h),
        m.dst ≠ a ∧ m.dst ≠ b ∧
          play (kqkPos a b c .black h) m = kqkPos a b m.dst .white (h + 1) ∧
          0 < wDepth a b m.dst ∧ wDepth a b m.dst < d) := by
  simp only [afterWhiteOK, Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨_, hok⟩ := hok
  have hlm : legalMoves (kqkPos a b c .black h) = legalMoves (kqkPos a b c .black 0) := rfl
  split at hok
  · rename_i hnil
    left
    simp only [isCheckmate, hlm, hnil, List.isEmpty_nil, Bool.and_true]
    exact hok
  · rename_i m₀ ms hcons
    right
    refine ⟨by rw [hlm, hcons]; simp, fun m hm => ?_⟩
    have hr := List.all_eq_true.1 hok m (by rw [← hcons, ← hlm]; exact hm)
    simp only [replyOK, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hr
    obtain ⟨⟨⟨⟨⟨⟨⟨hsrc, hpro⟩, hd₀⟩, hd₁⟩, hd₂⟩, hd₃⟩, hd₄⟩, hpos, hlt⟩ := hr
    have hm' : m = ⟨c, m.dst, none⟩ := by cases m; simp_all
    refine ⟨hd₀, hd₁, ?_, hpos, hlt⟩
    rw [hm']
    exact play_kqk_black a b c m.dst h hca hcb hd₀ hd₁ hd₂ hd₃ hd₄

/-! ### Positions on the lines and repetition -/

/-- A KQK board with distinct squares equals another KQK board only for the same squares. -/
theorem kqkBoard_inj {a b c a' b' c' : Square} (h₁ : a ≠ b) (h₂ : a ≠ c) (h₃ : b ≠ c)
    (H : kqkBoard a b c = kqkBoard a' b' c') : a = a' ∧ b = b' ∧ c = c' := by
  have ea : kqkBoard a' b' c' a = some ⟨.white, .king⟩ := by rw [← H]; simp [kqkBoard]
  have eb : kqkBoard a' b' c' b = some ⟨.white, .queen⟩ := by
    rw [← H]; simp [kqkBoard, Ne.symm h₁]
  have ec : kqkBoard a' b' c' c = some ⟨.black, .king⟩ := by
    rw [← H]; simp [kqkBoard, Ne.symm h₂, Ne.symm h₃]
  clear H
  unfold kqkBoard at ea eb ec
  refine ⟨?_, ?_, ?_⟩
  · split_ifs at ea <;> first | assumption | simp at ea
  · split_ifs at eb <;> first | assumption | simp at eb
  · split_ifs at ec <;> first | assumption | simp at ec

/-- A node of a line: a KQK position given by its squares, side to move and clock. -/
structure KQKNode where
  /-- White king. -/
  a : Square
  /-- White queen. -/
  b : Square
  /-- Black king. -/
  c : Square
  /-- Side to move. -/
  t : Color
  /-- Halfmove clock. -/
  h : Nat

/-- The position of a node. -/
def KQKNode.pos (e : KQKNode) : Position := kqkPos e.a e.b e.c e.t e.h

/-- The rank of a node. -/
def KQKNode.rank (e : KQKNode) : Nat := kqkRank e.a e.b e.c e.t

/-- The three squares of a node are distinct. -/
def KQKNode.Distinct (e : KQKNode) : Prop := e.a ≠ e.b ∧ e.a ≠ e.c ∧ e.b ≠ e.c

/-- Nodes in the same position (FIDE 9.2.3) have the same rank. -/
theorem KQKNode.rank_eq_of_same {e e' : KQKNode} (hd : e.Distinct)
    (hs : samePosition e.pos e'.pos = true) : e.rank = e'.rank := by
  rw [samePosition_iff] at hs
  simp only [key, KQKNode.pos, kqkPos, Prod.mk.injEq] at hs
  obtain ⟨ht, hb, _⟩ := hs
  obtain ⟨ha, hb', hc⟩ := kqkBoard_inj hd.1 hd.2.1 hd.2.2 hb
  simp only [KQKNode.rank, ha, hb', hc, ht]

/-- If no earlier position is the same as the current one, it has appeared once. -/
theorem repetitions_eq_one {g : GameState} (h : ∀ q ∈ g.history, samePosition g.pos q = false) :
    g.repetitions = 1 := by
  have hself : samePosition g.pos g.pos = true := (samePosition_iff _ _).2 rfl
  have hnil : g.history.filter (samePosition g.pos) = [] :=
    List.filter_eq_nil_iff.2 fun q hq => by simp [h q hq]
  simp [GameState.repetitions, hself, hnil]

/-- A position that has a legal move to a non-dead position is not dead. -/
theorem not_isDead_of_move {q : Position} {m : Move} (hm : m ∈ legalMoves q)
    (h : ¬ IsDead (play q m)) : ¬ IsDead q := by
  intro hd
  apply h
  intro ms r hr
  exact hd (m :: ms) r (by simp [playLegal, (isLegal_iff q m).2 hm, hr])

/-- A state with a legal move, clock below 150, no repetition and a non-dead position is not
terminal. -/
theorem not_terminal_of_rep {g : GameState} {m : Move} (hm : m ∈ legalMoves g.pos)
    (hh : g.pos.halfmove < 150) (hr : g.repetitions = 1) (hd : ¬ IsDead g.pos) :
    ¬ g.IsTerminal := by
  have hne : (legalMoves g.pos).isEmpty = false := by
    cases h : legalMoves g.pos with
    | nil => rw [h] at hm; simp at hm
    | cons => rfl
  have hcm : isCheckmate g.pos = false := by simp [isCheckmate, hne]
  have hsm : isStalemate g.pos = false := by simp [isStalemate, hne]
  have h150 : ¬ 150 ≤ g.pos.halfmove := by omega
  have had : g.automaticDraw = false := by
    simp [GameState.automaticDraw, hcm, hsm, hr, h150]
  simp only [GameState.IsTerminal, GameState.IsDraw, hcm, had]
  simp only [Bool.false_eq_true, false_or, true_and]
  exact hd

/-! ### The induction along the lines -/

/-- The node is on a line of the strategy: with White to move its depth is nonzero; with Black to
move it was reached by a White step accepted at some depth `d ≥ 1` (`afterWhiteOK`), and its rank
is below `2 d`. -/
def KQKNode.OK (e : KQKNode) : Prop :=
  match e.t with
  | .white => wDepth e.a e.b e.c ≠ 0
  | .black => ∃ d, 1 ≤ d ∧ afterWhiteOK kqkTable d e.a e.b e.c = true ∧
      2 * maxReplyDepth e.a e.b e.c + 1 ≤ 2 * d - 1

/-- **White wins along the certified lines**: from a game state whose current position is a node
on a line and whose earlier positions are nodes of larger rank, with clock plus rank at
most 150, White guarantees a win in `chessGame`. -/
theorem guarantees_of_node : ∀ r (cur : KQKNode) (hist : List KQKNode) (s : State),
    s.1 = ⟨cur.pos, hist.map KQKNode.pos⟩ → cur.Distinct → cur.OK → cur.rank = r →
    cur.h + r ≤ 150 → (∀ e ∈ hist, r < e.rank) →
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
    · have := KQKNode.rank_eq_of_same hdist hsp
      have := hhist e he
      omega
  obtain ⟨a, b, c, t, h⟩ := cur
  obtain ⟨h₁, h₂, h₃⟩ := hdist
  dsimp only at h₁ h₂ h₃ hh
  cases t with
  | white =>
    simp only [KQKNode.OK] at hok
    simp only [KQKNode.rank, kqkRank] at hr
    obtain ⟨m, hm, a', b', h₁', hca, hcb, hplay, hafter⟩ := white_step a b c h₁ h₂ h₃ hok h
    have hfm := table_sound kqkTable (fun i hi => (kqkTable_ok i hi).1) _ a b c rfl hok h
    have hpos : s.1.pos = kqkPos a b c .white h := by rw [hs]; rfl
    have hlt : s.1.pos.halfmove < 150 := by rw [hpos]; simp only [kqkPos]; omega
    have hnt : ¬ s.1.IsTerminal :=
      not_terminal_of_rep (m := m) (by rw [hpos]; exact hm) hlt hrep
        (by rw [hpos]; exact hfm.not_isDead)
    let t : State := ⟨s.1.play m, valid_play s.2 hnt m⟩
    refine Game.GuaranteesGe.first s t (by simp [chessGame, colorPlayer, hpos, kqkPos])
      (mem_chessMoves.2 ⟨hnt, m, by rw [hpos]; exact hm, rfl⟩) ?_
    -- the Black node
    have hmax : maxReplyDepth a' b' c < wDepth a b c := by
      rcases black_cases a' b' c _ hca hcb hafter 0 with hmate | ⟨_, hall⟩
      · have : legalMoves (kqkPos a' b' c .black 0) = [] := by
          simp only [isCheckmate, Bool.and_eq_true, List.isEmpty_iff] at hmate
          exact hmate.2
        simp only [maxReplyDepth, this, List.map_nil, List.foldr_nil]
        omega
      · have : maxReplyDepth a' b' c ≤ wDepth a b c - 1 :=
          foldr_max_le fun x hx => by
            simp only [List.mem_map] at hx
            obtain ⟨m', hm', rfl⟩ := hx
            have := (hall m' hm').2.2.2
            omega
        omega
    refine ih (2 * maxReplyDepth a' b' c + 1) (by omega) ⟨a', b', c, .black, h + 1⟩
      (⟨a, b, c, .white, h⟩ :: hist) t ?_ ⟨h₁', Ne.symm hca, Ne.symm hcb⟩
      ⟨wDepth a b c, by omega, hafter, by dsimp only; omega⟩ rfl (by simp only; omega) ?_
    · change s.1.play m = _
      simp only [GameState.play, hs, List.map_cons]
      rw [show (⟨a, b, c, .white, h⟩ : KQKNode).pos = kqkPos a b c .white h from rfl]
      rw [show (⟨a', b', c, .black, h + 1⟩ : KQKNode).pos = kqkPos a' b' c .black (h + 1) from rfl]
      rw [← hplay]
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · simp only [KQKNode.rank, kqkRank]; omega
      · have := hhist e he; omega
  | black =>
    simp only [KQKNode.OK] at hok
    obtain ⟨d, hd1, hafter, hdr⟩ := hok
    simp only [KQKNode.rank, kqkRank] at hr
    have hpos : s.1.pos = kqkPos a b c .black h := by rw [hs]; rfl
    rcases black_cases a b c d (Ne.symm h₂) (Ne.symm h₃) hafter h with hmate | ⟨hne, hall⟩
    · refine Game.GuaranteesGe.terminal s ?_ ?_
      · exact (chessMoves_eq_nil_iff s).2 (Or.inl (by rw [hpos]; exact hmate))
      · have hm' := hmate
        simp only [kqkPos] at hm'
        simp [chessGame, chessOutcome, hpos, hm', kqkPos, matedOutcome]
    · obtain ⟨m₀, hm₀⟩ := List.exists_mem_of_ne_nil _ hne
      obtain ⟨_, _, hp₀, hpos₀, _⟩ := hall m₀ hm₀
      have hfm := table_sound kqkTable (fun i hi => (kqkTable_ok i hi).1) _ a b m₀.dst rfl
        (Nat.pos_iff_ne_zero.mp hpos₀) (h + 1)
      have hlt : s.1.pos.halfmove < 150 := by rw [hpos]; simp only [kqkPos]; omega
      have hnt : ¬ s.1.IsTerminal := by
        refine not_terminal_of_rep (m := m₀) (by rw [hpos]; exact hm₀) hlt hrep ?_
        rw [hpos]
        exact not_isDead_of_move hm₀ (by rw [hp₀]; exact hfm.not_isDead)
      refine Game.GuaranteesGe.second s
        (fun h0 => hnt ((chessMoves_eq_nil_iff s).1 h0))
        (by simp [chessGame, colorPlayer, hpos, kqkPos]) fun u hu => ?_
      obtain ⟨_, m, hm, hu⟩ := mem_chessMoves.1 hu
      rw [hpos] at hm
      obtain ⟨hda, hdb, hp, hpos', hlt⟩ := hall m hm
      have hle : wDepth a b m.dst ≤ maxReplyDepth a b c :=
        le_foldr_max (List.mem_map.2 ⟨m, hm, rfl⟩)
      refine ih (2 * wDepth a b m.dst) (by omega) ⟨a, b, m.dst, .white, h + 1⟩
        (⟨a, b, c, .black, h⟩ :: hist) u ?_ ⟨h₁, Ne.symm hda, Ne.symm hdb⟩
        (by dsimp only [KQKNode.OK]; omega) rfl (by simp only; omega) ?_
      · rw [hu]
        simp only [GameState.play, hs, List.map_cons]
        rw [show (⟨a, b, c, .black, h⟩ : KQKNode).pos = kqkPos a b c .black h from rfl]
        rw [show (⟨a, b, m.dst, .white, h + 1⟩ : KQKNode).pos =
          kqkPos a b m.dst .white (h + 1) from rfl]
        rw [← hp]
      · intro e he
        rcases List.mem_cons.1 he with rfl | he
        · simp only [KQKNode.rank, kqkRank]; omega
        · have := hhist e he; omega

/-! ### Main theorems -/

/-- **King and queen versus king in the full game** (rule model `A`): from the start of a game in
a KQK position with White to move, the black king not attacked and halfmove clock at most 130,
White can force a win, and the value of the game is `whiteWins`. -/
theorem kqk_game_whiteWins (a b c : Square) (h₁ : a ≠ b) (h₂ : a ≠ c) (h₃ : b ≠ c)
    (hc : attackedBy (kqkBoard a b c) .white c = false) (h : Nat) (hh : h ≤ 130) :
    chessGame.MaxForces .whiteWins (State.start (kqkPos a b c .white h)) ∧
      chessGame.value (State.start (kqkPos a b c .white h)) = .whiteWins := by
  have hi : kqkIdx a.val b.val c.val < 262144 := by
    have := a.isLt; have := b.isLt; have := c.isLt; simp only [kqkIdx]; omega
  obtain ⟨hs, hcov⟩ := kqkTable_ok _ hi
  obtain ⟨e₁, e₂, e₃⟩ := sqOf_kqkIdx a b c
  simp only [coverOK, e₁, e₂, e₃, hc, Bool.or_eq_true, beq_iff_eq, h₁, h₂, h₃, false_or,
    bne_iff_ne, ne_eq, Bool.false_eq_true] at hcov
  have hle : wDepth a b c ≤ 10 := by
    simp only [stateOK, Bool.or_eq_true, beq_iff_eq, hcov, false_or, Bool.and_eq_true,
      decide_eq_true_eq] at hs
    exact hs.1.1.1.1
  have hg := guarantees_of_node (2 * wDepth a b c) ⟨a, b, c, .white, h⟩ []
    (State.start (kqkPos a b c .white h)) rfl ⟨h₁, h₂, h₃⟩ hcov rfl (by simp only; omega)
    (by simp)
  have hv := (chessGame.guaranteesGe_iff _ _).1 hg
  exact ⟨(chessGame.maxForces_iff _ _).2 hv, (chessGame.maxForces_whiteWins_iff _).1
    ((chessGame.maxForces_iff _ _).2 hv)⟩

/-- **King and queen versus king in the full game, for well-formed positions**: from the start of a
game in any well-formed position whose pieces are a white king, a white queen and a black king,
with White to move, no castling rights and halfmove clock at most 130, White can force a win in
`chessGame`, whose value there is `whiteWins`. -/
theorem kqk_game_whiteWins_wellFormed (p : Position) (a b c : Square) (h₁ : a ≠ b) (h₂ : a ≠ c)
    (h₃ : b ≠ c) (hb : p.board = kqkBoard a b c) (ht : p.turn = .white)
    (hcr : p.castling = .none) (hw : wellFormed p = true) (hh : p.halfmove ≤ 130) :
    chessGame.MaxForces .whiteWins (State.start p) ∧
      chessGame.value (State.start p) = .whiteWins := by
  have hep := epTarget_eq_none_of_kqk hb hw
  have hc : attackedBy (kqkBoard a b c) .white c = false := by
    simp only [wellFormed, Bool.and_eq_true, Bool.not_eq_true'] at hw
    have := hw.1.2
    rw [ht, hb] at this
    simpa [inCheck, Color.other, kingSquare_kqk_black a b c h₂ h₃] using this
  have hp : p = kqkPos a b c .white p.halfmove := by
    cases p; simp_all [kqkPos]
  rw [hp]
  exact kqk_game_whiteWins a b c h₁ h₂ h₃ hc p.halfmove hh

end LeanTheory.Chess
