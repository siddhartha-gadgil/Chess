/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.Chess.Game
public import LeanTheory.Theory.Games.Determinacy
public import LeanTheory.Certificates.KernelFact
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Chess under rule model A is a determined finite game (Zermelo)

The chess instance of note `N-04` (goal `G-3(a)`), on top of the kernel `Kernel/Chess/Game`
(model `A` of `N-03`) and the abstract backward induction of `Theory/Games/Determinacy`.

* `key`: the data compared by `samePosition` (FIDE 9.2.3), in a finite type `Key`;
  `samePosition_iff` shows that two positions are the same exactly when their keys agree, so
  `repetitions` counts keys (`repetitions_eq_count`).
* `Valid g`: every position class occurs at most 4 times in the history of `g`. This holds at
  the start of a game and is preserved by every move from a non-terminal state, because a
  non-terminal state is not a fivefold repetition (`valid_play`). Hence the history of a valid
  state has at most `4 * Fintype.card Key` positions (`history_length_le`, pigeonhole): the
  **fivefold-repetition rule alone bounds the length of every game**; the 75-move rule is not
  used for finiteness.
* `chessGame : Game State Outcome`: states are valid game states, White is the first
  (maximizing) player, a state has no successors exactly when it is terminal in the sense of
  `GameState.IsTerminal` (`chessMoves_eq_nil_iff`), and the outcome of a checkmate is a win for
  the side not to move, every other terminal state is a draw.
* `chess_determined`, `chess_determined_initial`: **Zermelo for chess**: from every valid state,
  in particular from the initial position, exactly one of "White can force a win", "Black can
  force a win", "both can force at least a draw" holds.
* Meaning checks: `chessGame_value_of_terminal`, `chessGame_value_of_checkmate`, and Fool's mate
  as a play of `chessGame` (`foolsMate_mem_moves`), after whose third move Black can force a win
  (`foolsMate_black_forces_win`).

Scope: the value `chessGame.value initialState` is **not computed**; the theorems say only that
it exists and is forced by both players (question `Q-5` stays open). Being terminal involves the
semantic dead-position rule `IsDead`, decided classically, so `chessGame` is noncomputable.
Strategies are positional over states carrying the full history, so they cover
history-dependent play.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.Chess

open LeanTheory.Games

/-! ### Finiteness of the rule types -/

/-- There are two colours. -/
instance fintypeColor : Fintype Color :=
  Fintype.ofList [.white, .black] (by intro c; cases c <;> simp)

/-- There are six kinds of pieces. -/
instance fintypePieceType : Fintype PieceType :=
  Fintype.ofList [.pawn, .knight, .bishop, .rook, .queen, .king] (by intro k; cases k <;> simp)

/-- Pieces are finite: a piece is a colour and a kind. -/
instance fintypePiece : Fintype Piece :=
  Fintype.ofSurjective (fun x : Color × PieceType => ⟨x.1, x.2⟩) fun p => ⟨(p.1, p.2), rfl⟩

/-- Castling rights are finite: four flags. -/
instance fintypeCastlingRights : Fintype CastlingRights :=
  Fintype.ofSurjective (fun x : Bool × Bool × Bool × Bool => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩)
    fun c => ⟨(c.1, c.2, c.3, c.4), rfl⟩

/-- Moves are finite: source, destination and optional promotion piece. -/
instance fintypeMove : Fintype Move :=
  Fintype.ofSurjective (fun x : Square × Square × Option PieceType => ⟨x.1, x.2.1, x.2.2⟩)
    fun m => ⟨(m.1, m.2, m.3), rfl⟩

/-! ### Position keys -/

/-- The data compared by `samePosition` (FIDE 9.2.3): side to move, placement, castling rights
and the set of legal moves. -/
abbrev Key := Color × Board × CastlingRights × Finset Move

/-- The key of a position. -/
def key (p : Position) : Key := (p.turn, p.board, p.castling, (legalMoves p).toFinset)

/-- `boardEq` decides equality of boards. -/
theorem boardEq_iff (b b' : Board) : boardEq b b' = true ↔ b = b' := by
  simp [boardEq, List.all_eq_true, mem_allSquares, funext_iff]

/-- `sameMoves` decides equality of the sets of moves. -/
theorem sameMoves_iff (l l' : List Move) : sameMoves l l' = true ↔ l.toFinset = l'.toFinset := by
  simp only [sameMoves, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
    Finset.ext_iff, List.mem_toFinset]
  exact ⟨fun h a => ⟨h.1 a, h.2 a⟩, fun h => ⟨fun a => (h a).1, fun a => (h a).2⟩⟩

/-- **Two positions are the same (FIDE 9.2.3) exactly when their keys agree.** -/
theorem samePosition_iff (p q : Position) : samePosition p q = true ↔ key p = key q := by
  simp [samePosition, boardEq_iff, sameMoves_iff, key, and_assoc]

/-- The number of positions in `l` that are the same as `q` is the number of occurrences of the
key of `q` among the keys of `l`. -/
theorem length_filter_samePosition (q : Position) (l : List Position) :
    (l.filter (samePosition q)).length = (l.map key).count (key q) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases h : key q = key x
    · have h' : samePosition q x = true := (samePosition_iff q x).2 h
      simp [h', ih, h]
    · have h' : samePosition q x = false := by
        rw [← Bool.not_eq_true, samePosition_iff]; exact h
      simp [h', ih, Ne.symm h]

/-- The repetition count of a game state counts the key of the current position. -/
theorem repetitions_eq_count (g : GameState) :
    g.repetitions = (g.history.map key).count (key g.pos) + 1 := by
  rw [GameState.repetitions, length_filter_samePosition]
  simp

/-! ### Valid states and the length bound -/

/-- A game state is **valid** when every position class (key) occurs at most 4 times in its
history. Every game played under model `A` from a start state has this property, since a game
does not continue from a fivefold repetition (`valid_start`, `valid_play`). -/
def Valid (g : GameState) : Prop := ∀ k : Key, (g.history.map key).count k ≤ 4

/-- A state with at most 4 earlier positions is valid. -/
theorem valid_of_length_le {g : GameState} (h : g.history.length ≤ 4) : Valid g :=
  fun k => le_trans (List.count_le_length) (by simpa using h)

/-- The start of a game is valid. -/
theorem valid_start (p : Position) : Valid (GameState.start p) :=
  valid_of_length_le (by simp [GameState.start])

/-- A non-terminal state is not a fivefold repetition. -/
theorem repetitions_lt_of_not_terminal {g : GameState} (h : ¬ g.IsTerminal) :
    g.repetitions < 5 := by
  by_contra hr
  apply h
  by_cases hc : isCheckmate g.pos = true
  · exact Or.inl hc
  · refine Or.inr (Or.inl ?_)
    simp only [GameState.automaticDraw, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true,
      decide_eq_true_eq]
    exact ⟨by simpa using hc, Or.inr (by omega)⟩

/-- **Validity is preserved by every move from a non-terminal state.** -/
theorem valid_play {g : GameState} (hv : Valid g) (h : ¬ g.IsTerminal) (m : Move) :
    Valid (g.play m) := by
  have hr := repetitions_lt_of_not_terminal h
  rw [repetitions_eq_count] at hr
  intro k
  simp only [GameState.play, List.map_cons, List.count_cons, beq_iff_eq]
  by_cases hk : key g.pos = k
  · subst hk
    simp only [ite_true]
    omega
  · simp only [hk, ite_false]
    simpa using hv k

/-- **Pigeonhole**: a valid state has at most `4 * |Key|` earlier positions. -/
theorem history_length_le {g : GameState} (hv : Valid g) :
    g.history.length ≤ 4 * Fintype.card Key := by
  classical
  let m : Multiset Key := (g.history.map key : List Key)
  have hcard : g.history.length = Multiset.card m := by simp [m]
  rw [hcard, ← Multiset.toFinset_sum_count_eq]
  calc ∑ a ∈ m.toFinset, m.count a ≤ ∑ _a ∈ m.toFinset, 4 :=
        Finset.sum_le_sum fun a _ => by simpa [m] using hv a
    _ = m.toFinset.card * 4 := Finset.sum_const_nat fun _ _ => rfl
    _ ≤ Fintype.card Key * 4 := Nat.mul_le_mul_right _ (Finset.card_le_univ _)
    _ = 4 * Fintype.card Key := Nat.mul_comm _ _

/-! ### The chess game -/

/-- States of the chess game: valid game states (position plus history). -/
abbrev State := {g : GameState // Valid g}

/-- The state at the start of a game from position `p`. -/
def State.start (p : Position) : State := ⟨GameState.start p, valid_start p⟩

/-- The state at the start of a game from the initial position. -/
def initialState : State := State.start initialPosition

/-- White is the first (maximizing) player, Black the second. -/
def colorPlayer : Color → Player
  | .white => .first
  | .black => .second

/-- The outcome when the player `c` to move is checkmated: the other player wins. -/
def matedOutcome : Color → Outcome
  | .white => .blackWins
  | .black => .whiteWins

open Classical in
/-- Successor states: none at a terminal state (checkmate, automatic draw or dead position),
otherwise the states after each legal move. -/
def chessMoves (s : State) : List State :=
  if h : s.1.IsTerminal then []
  else (legalMoves s.1.pos).map fun m => ⟨s.1.play m, valid_play s.2 h m⟩

/-- The outcome of a terminal state: checkmate is a win for the side not to move, every other
end of the game is a draw. -/
def chessOutcome (s : State) : Outcome :=
  if isCheckmate s.1.pos = true then matedOutcome s.1.pos.turn else .draw

/-- The successors of a state are the states after the legal moves, if it is not terminal. -/
theorem mem_chessMoves {s t : State} :
    t ∈ chessMoves s ↔ ¬ s.1.IsTerminal ∧ ∃ m ∈ legalMoves s.1.pos, t.1 = s.1.play m := by
  unfold chessMoves
  split
  · simp_all
  · rename_i h
    simp only [List.mem_map, h, not_false_eq_true, true_and]
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, hm, rfl⟩
    · rintro ⟨m, hm, ht⟩
      exact ⟨m, hm, Subtype.ext ht.symm⟩

/-- **Chess under rule model `A` as a finite game**: White maximizes, moves are legal moves
from non-terminal states, and the remaining depth is bounded by `4 * |Key|` minus the length of
the history (fivefold-repetition bound). -/
def chessGame : Game State Outcome where
  toMove s := colorPlayer s.1.pos.turn
  moves := chessMoves
  outcome := chessOutcome
  bound s := 4 * Fintype.card Key - s.1.history.length
  bound_lt s t ht := by
    obtain ⟨-, m, -, ht⟩ := mem_chessMoves.1 ht
    have h1 := history_length_le t.2
    have h2 : t.1.history.length = s.1.history.length + 1 := by
      rw [ht]; rfl
    omega

/-- A state has no successors exactly when it is terminal: a non-terminal position always has
a legal move, because no legal move means checkmate or stalemate. -/
theorem chessMoves_eq_nil_iff (s : State) : chessMoves s = [] ↔ s.1.IsTerminal := by
  unfold chessMoves
  split
  · simp_all
  · rename_i h
    simp only [List.map_eq_nil_iff, h, iff_false]
    intro hl
    apply h
    by_cases hc : inCheck s.1.pos.board s.1.pos.turn = true
    · exact Or.inl (by simp [isCheckmate, hc, hl])
    · refine Or.inr (Or.inl ?_)
      simp [GameState.automaticDraw, isCheckmate, isStalemate, hc, hl]

/-! ### Determinacy -/

/-- **Zermelo for chess (model `A`)**: from every valid state exactly one holds: White can force
a win, Black can force a win, or both can force at least a draw. The value itself is not
computed. -/
theorem chess_determined (s : State) :
    (chessGame.MaxForces .whiteWins s ∧ ¬ chessGame.MinForces .blackWins s ∧
        ¬ (chessGame.MaxForces .draw s ∧ chessGame.MinForces .draw s)) ∨
      (¬ chessGame.MaxForces .whiteWins s ∧ chessGame.MinForces .blackWins s ∧
        ¬ (chessGame.MaxForces .draw s ∧ chessGame.MinForces .draw s)) ∨
      (¬ chessGame.MaxForces .whiteWins s ∧ ¬ chessGame.MinForces .blackWins s ∧
        (chessGame.MaxForces .draw s ∧ chessGame.MinForces .draw s)) :=
  chessGame.exactly_one_outcome s

/-- **Chess is determined (`G-3(a)`)**: from the initial position exactly one holds: White can
force a win, Black can force a win, or both can force at least a draw. Which one is open
(`Q-5`). -/
theorem chess_determined_initial :
    (chessGame.MaxForces .whiteWins initialState ∧ ¬ chessGame.MinForces .blackWins initialState ∧
        ¬ (chessGame.MaxForces .draw initialState ∧ chessGame.MinForces .draw initialState)) ∨
      (¬ chessGame.MaxForces .whiteWins initialState ∧
        chessGame.MinForces .blackWins initialState ∧
        ¬ (chessGame.MaxForces .draw initialState ∧ chessGame.MinForces .draw initialState)) ∨
      (¬ chessGame.MaxForces .whiteWins initialState ∧
        ¬ chessGame.MinForces .blackWins initialState ∧
        (chessGame.MaxForces .draw initialState ∧ chessGame.MinForces .draw initialState)) :=
  chess_determined initialState

/-- The value of chess is forced by both players: White guarantees at least it, Black at most
it. -/
theorem chess_value_forced (s : State) :
    chessGame.MaxForces (chessGame.value s) s ∧ chessGame.MinForces (chessGame.value s) s :=
  chessGame.forces_value s

/-! ### Meaning checks -/

/-- At a terminal state the value is the outcome. -/
theorem chessGame_value_of_terminal {s : State} (h : s.1.IsTerminal) :
    chessGame.value s = chessOutcome s :=
  chessGame.value_of_terminal ((chessMoves_eq_nil_iff s).2 h)

/-- At a checkmate the side not to move has won. -/
theorem chessGame_value_of_checkmate {s : State} (h : isCheckmate s.1.pos = true) :
    chessGame.value s = matedOutcome s.1.pos.turn := by
  rw [chessGame_value_of_terminal (Or.inl h), chessOutcome]
  simp [h]

/-- A position from which some sequence of legal moves reaches a checkmate is not dead. -/
theorem not_isDead_of_mate {p : Position} {ms : List Move}
    (h : (playLegal p ms).map isCheckmate = some true) : ¬ IsDead p := by
  intro hd
  cases hq : playLegal p ms with
  | none => simp [hq] at h
  | some q =>
    simp only [hq, Option.map_some, Option.some.injEq] at h
    rw [hd ms q hq] at h
    exact Bool.false_ne_true h

/-- A state is not terminal if the position has a legal move, the halfmove clock is below 150,
the history has fewer than 4 positions and the position is not dead. -/
theorem not_terminal_of {g : GameState} {m : Move} (hm : m ∈ legalMoves g.pos)
    (hh : g.pos.halfmove < 150) (hl : g.history.length < 4) (hd : ¬ IsDead g.pos) :
    ¬ g.IsTerminal := by
  have hne : (legalMoves g.pos).isEmpty = false :=
    List.isEmpty_eq_false_iff.2 (List.ne_nil_of_mem hm)
  have hc : isCheckmate g.pos = false := by simp [isCheckmate, hne]
  have hs : isStalemate g.pos = false := by simp [isStalemate, hne]
  have hr : g.repetitions < 5 := by
    have := List.length_filter_le (samePosition g.pos) (g.pos :: g.history)
    simp only [List.length_cons] at this
    rw [GameState.repetitions]
    omega
  rintro (h | (h | ⟨-, h⟩))
  · rw [hc] at h; exact Bool.false_ne_true h
  · simp only [GameState.automaticDraw, hc, hs, Bool.not_false, Bool.true_and, Bool.false_or,
      Bool.or_eq_true, decide_eq_true_eq] at h
    omega
  · exact hd h

/-- The moves of Fool's mate: 1. f3 e5 2. g4 Qh4#. -/
def foolsMateMove : ℕ → Move
  | 0 => mv 5 2 5 3
  | 1 => mv 4 7 4 5
  | 2 => mv 6 2 6 4
  | _ => mv 3 8 7 4

/-- The game state after the first `n` moves of Fool's mate. -/
def foolsMateGame : ℕ → GameState
  | 0 => GameState.start initialPosition
  | n + 1 => (foolsMateGame n).play (foolsMateMove n)

/-- After `n` moves of Fool's mate the history has `n` positions. -/
theorem foolsMateGame_history_length (n : ℕ) : (foolsMateGame n).history.length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [foolsMateGame, GameState.play, ih]

/-- The state after the first `n ≤ 4` moves of Fool's mate. -/
def foolsMateState (n : ℕ) (h : n ≤ 4) : State :=
  ⟨foolsMateGame n, valid_of_length_le (by rw [foolsMateGame_history_length]; exact h)⟩

/-- Before each move of Fool's mate: the move is legal, the halfmove clock is small and the
remaining moves reach checkmate. -/
theorem foolsMate_facts : ∀ n < 4,
    isLegal (foolsMateGame n).pos (foolsMateMove n) = true ∧
      (foolsMateGame n).pos.halfmove < 150 ∧
      (playLegal (foolsMateGame n).pos (((List.range 4).map foolsMateMove).drop n)).map
        isCheckmate = some true := by
  kernel_fact

/-- The final position of Fool's mate is checkmate with White to move. -/
theorem foolsMate_final : isCheckmate (foolsMateGame 4).pos = true ∧
    (foolsMateGame 4).pos.turn = .white := by
  kernel_fact

/-- The start of Fool's mate is the initial state. -/
theorem foolsMateState_zero : foolsMateState 0 (by omega) = initialState := rfl

/-- **Fool's mate is a play of `chessGame`**: each state is a successor of the previous one. -/
theorem foolsMate_mem_moves (n : ℕ) (h : n < 4) :
    foolsMateState (n + 1) h ∈ chessGame.moves (foolsMateState n h.le) := by
  obtain ⟨hl, hh, hd⟩ := foolsMate_facts n h
  have hm := (isLegal_iff _ _).1 hl
  refine mem_chessMoves.2 ⟨not_terminal_of hm hh ?_ (not_isDead_of_mate hd), _, hm, rfl⟩
  change (foolsMateGame n).history.length < 4
  rw [foolsMateGame_history_length]
  exact h

/-- The final state of Fool's mate has value `blackWins`. -/
theorem foolsMate_value_final : chessGame.value (foolsMateState 4 le_rfl) = .blackWins := by
  rw [chessGame_value_of_checkmate foolsMate_final.1]
  change matedOutcome (foolsMateGame 4).pos.turn = _
  rw [foolsMate_final.2]
  rfl

/-- **After 1. f3 e5 2. g4, Black can force a win** (by 2... Qh4#). -/
theorem foolsMate_black_forces_win :
    chessGame.MinForces .blackWins (foolsMateState 3 (by omega)) := by
  rw [Game.minForces_blackWins_iff]
  have hle := chessGame.le_value_of_second (s := foolsMateState 3 (by omega))
    (by
      change colorPlayer (foolsMateGame 3).pos.turn = _
      rw [show (foolsMateGame 3).pos.turn = .black by kernel_fact]
      rfl)
    (foolsMate_mem_moves 3 (by omega))
  rw [foolsMate_value_final] at hle
  exact le_antisymm hle (Outcome.le_iff_toNat.2 (Nat.zero_le _))

end LeanTheory.Chess
