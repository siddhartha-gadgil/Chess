/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.Chess.Rules

/-!
# Kernel: well-formed positions, game states, draw rules and forced mates

**This is a kernel file** (note `N-03`), on top of the rules kernel `Kernel/Chess/Rules`. It fixes
the rule model `A` chosen for question `Q-1`: the game ends by checkmate (FIDE 5.1.1), stalemate
(5.2.1), dead position (5.2.2), fivefold repetition (9.6.1) or the 75-move rule (9.6.2, with
checkmate taking precedence). Claimable draws (9.2, 9.3) are not part of the model.

* `wellFormed`: exactly one king of each colour, no pawn on the first or last rank, the side not
  to move is not in check, and the en passant target is consistent with a double step just made.
  Resolves audit finding `A-1`: theorems about outcomes assume `wellFormed p = true`.
* `samePosition` (FIDE 9.2.3): same side to move, same placement, same castling rights and the
  same legal moves for the side to move. Comparing legal moves (not the `epTarget` field) resolves
  audit finding `A-2`. Comparing castling-right *flags* is a modelling choice (correction `C-5`).
* `GameState`: a position with the list of earlier positions (most recent first);
  `repetitions`, `automaticDraw` (stalemate, 75-move, fivefold), the semantic `IsDead` and
  `IsDraw`.
* `ForcesMate c n p`: player `c` can force checkmate of the opponent within `n` moves of `c`,
  against every defence (an AND–OR inductive). `forcesMateB` is a computable checker with the
  soundness theorem `forcesMateB_sound`; `ForcesMate.not_isDead` shows that the dead-position
  rule never interrupts a forced mate.

The game-theoretic model with draw rules (`ForcesMate` lifted to game states, the chess `Game` of
`Theory/Games/Determinacy`) is built on these definitions in later files.
-/

@[expose] public section

namespace LeanTheory.Chess

/-! ### Well-formed positions -/

/-- The number of squares holding the piece `pc`. -/
def countPiece (b : Board) (pc : Piece) : Nat := (allSquares.filter fun s => b s == some pc).length

/-- No pawn stands on the first or last rank. -/
def pawnsOnBoard (b : Board) : Bool :=
  allSquares.all fun s =>
    !(b s == some ⟨.white, .pawn⟩ || b s == some ⟨.black, .pawn⟩) || (s.rank != 0 && s.rank != 7)

/-- The en passant target, if any, is the square just passed over by an opponent pawn's double
step: it is on the right rank and empty, the opponent pawn stands just beyond it and the pawn's
starting square is empty. -/
def epConsistent (p : Position) : Bool :=
  match p.epTarget with
  | none => true
  | some t =>
    let o := p.turn.other
    t.rank == (match o with | .white => 2 | .black => 5) && p.board t == none &&
      (match t.shift 0 o.forward with
        | some u => p.board u == some ⟨o, .pawn⟩
        | none => false) &&
      (match t.shift 0 (-o.forward) with
        | some u => p.board u == none
        | none => false)

/-- **Well-formed positions**: one king of each colour, pawns not on the first or last rank, the
side not to move not in check, and a consistent en passant target. Reachability from the initial
position (FIDE 3.10.3) is *not* required (question `Q-3`). -/
def wellFormed (p : Position) : Bool :=
  countPiece p.board ⟨.white, .king⟩ == 1 && countPiece p.board ⟨.black, .king⟩ == 1 &&
    pawnsOnBoard p.board && !inCheck p.board p.turn.other && epConsistent p

/-! ### Repetition (FIDE 9.2.3) -/

/-- The two boards have the same piece on every square. -/
def boardEq (b b' : Board) : Bool := allSquares.all fun s => b s == b' s

/-- The two lists contain the same moves (as sets). -/
def sameMoves (l l' : List Move) : Bool := l.all l'.contains && l'.all l.contains

/-- **The same position** in the sense of FIDE 9.2.3: same player to move, same pieces on the
same squares, same castling rights, and the same legal moves for the player to move (so an en
passant target with no legal en passant capture is ignored). -/
def samePosition (p q : Position) : Bool :=
  p.turn == q.turn && boardEq p.board q.board && p.castling == q.castling &&
    sameMoves (legalMoves p) (legalMoves q)

/-! ### Game states and draws -/

/-- A game state: the current position and the earlier positions of the game, most recent
first. -/
structure GameState where
  /-- The current position. -/
  pos : Position
  /-- The earlier positions, most recent first. -/
  history : List Position

/-- The game state at the start of a game from position `p`. -/
def GameState.start (p : Position) : GameState := ⟨p, []⟩

/-- The game state after the move `m`. -/
def GameState.play (g : GameState) (m : Move) : GameState :=
  ⟨Chess.play g.pos m, g.pos :: g.history⟩

/-- Play a sequence of moves from a game state, failing if one of them is not legal. -/
def GameState.playLegal : GameState → List Move → Option GameState
  | g, [] => some g
  | g, m :: ms => if isLegal g.pos m then GameState.playLegal (g.play m) ms else none

/-- How many times the current position has appeared in the game (including now). -/
def GameState.repetitions (g : GameState) : Nat :=
  ((g.pos :: g.history).filter (samePosition g.pos)).length

/-- **Automatic draws decided from the game record**: stalemate (5.2.1), fivefold repetition
(9.6.1) and 75 moves by each player without pawn move or capture (9.6.2). Checkmate takes
precedence. -/
def GameState.automaticDraw (g : GameState) : Bool :=
  !isCheckmate g.pos &&
    (isStalemate g.pos || 150 ≤ g.pos.halfmove || 5 ≤ g.repetitions)

/-- **Dead position** (FIDE 5.2.2): no sequence of legal moves leads to a checkmate (of either
player). A semantic, generally non-computable condition. -/
def IsDead (p : Position) : Prop :=
  ∀ ms q, playLegal p ms = some q → isCheckmate q = false

/-- The game is drawn at this state (model `A`). -/
def GameState.IsDraw (g : GameState) : Prop :=
  g.automaticDraw = true ∨ (isCheckmate g.pos = false ∧ IsDead g.pos)

/-- The game has ended at this state: checkmate or a draw. -/
def GameState.IsTerminal (g : GameState) : Prop := isCheckmate g.pos = true ∨ g.IsDraw

/-! ### Forced mates -/

/-- **`c` forces mate within `n` moves**: player `c` has a strategy that checkmates the opponent
after at most `n` moves of `c`, whatever the opponent plays. Counting only `c`'s moves, a
position where the opponent is to move and already checkmated needs `0` moves. -/
inductive ForcesMate (c : Color) : Nat → Position → Prop where
  /-- The opponent is to move and is checkmated. -/
  | mated (n : Nat) (p : Position) : p.turn = c.other → isCheckmate p = true → ForcesMate c n p
  /-- `c` is to move and has a legal move after which it forces mate within `n` moves. -/
  | attack (n : Nat) (p : Position) (m : Move) : p.turn = c → m ∈ legalMoves p →
      ForcesMate c n (play p m) → ForcesMate c (n + 1) p
  /-- The opponent is to move, has a legal move, and after each legal move `c` forces mate
  within `n` moves. -/
  | defend (n : Nat) (p : Position) : p.turn = c.other → legalMoves p ≠ [] →
      (∀ m ∈ legalMoves p, ForcesMate c n (play p m)) → ForcesMate c n p

/-- Search for a forced mate, `c` to move: some legal move leads to a checkmate, or to a position
with legal replies all of which allow a forced mate within `n - 1` further moves. -/
def attackB (c : Color) : Nat → Position → Bool
  | 0, _ => false
  | n + 1, p =>
    (legalMoves p).any fun m =>
      let q := play p m
      isCheckmate q ||
        (!(legalMoves q).isEmpty && (legalMoves q).all fun m' => attackB c n (play q m'))

/-- **Computable forced-mate checker** (exponential; for small fixtures). -/
def forcesMateB (c : Color) (n : Nat) (p : Position) : Bool :=
  if p.turn = c then attackB c n p
  else
    isCheckmate p ||
      (!(legalMoves p).isEmpty && (legalMoves p).all fun m => attackB c n (play p m))

/-! ### Basic facts -/

/-- A move passes the turn to the opponent. -/
theorem turn_play (p : Position) (m : Move) : (play p m).turn = p.turn.other := rfl

/-- The opponent of the opponent. -/
@[simp] theorem Color.other_other (c : Color) : c.other.other = c := by cases c <;> rfl

/-- No player is its own opponent. -/
theorem Color.other_ne (c : Color) : c.other ≠ c := by cases c <;> simp [Color.other]

/-- `isLegal` is membership in `legalMoves`. -/
theorem isLegal_iff (p : Position) (m : Move) : isLegal p m = true ↔ m ∈ legalMoves p := by
  simp [isLegal]

/-- Soundness of `attackB`. -/
theorem attackB_sound (c : Color) :
    ∀ n p, p.turn = c → attackB c n p = true → ForcesMate c n p := by
  intro n
  induction n with
  | zero => intro p _ h; simp [attackB] at h
  | succ n ih =>
    intro p hp h
    simp only [attackB, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
      List.isEmpty_eq_false_iff, List.all_eq_true] at h
    obtain ⟨m, hm, h⟩ := h
    have hq : (play p m).turn = c.other := by rw [turn_play, hp]
    refine ForcesMate.attack n p m hp hm ?_
    rcases h with h | ⟨hne, hall⟩
    · exact ForcesMate.mated n _ hq h
    · refine ForcesMate.defend n _ hq hne fun m' hm' => ih _ ?_ (hall m' hm')
      rw [turn_play, hq, Color.other_other]

/-- **Soundness of the forced-mate checker.** -/
theorem forcesMateB_sound (c : Color) (n : Nat) (p : Position) (h : forcesMateB c n p = true) :
    ForcesMate c n p := by
  unfold forcesMateB at h
  by_cases hp : p.turn = c
  · simp only [hp, ite_true] at h
    exact attackB_sound c n p hp h
  · simp only [hp, ite_false, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
      List.isEmpty_eq_false_iff, List.all_eq_true] at h
    have hp' : p.turn = c.other := by
      cases c <;> cases h' : p.turn <;> simp_all [Color.other]
    rcases h with h | ⟨hne, hall⟩
    · exact ForcesMate.mated n p hp' h
    · refine ForcesMate.defend n p hp' hne fun m hm => attackB_sound c n _ ?_ (hall m hm)
      rw [turn_play, hp', Color.other_other]

/-- A player to move cannot have forced mate within `0` moves. -/
theorem ForcesMate.not_zero {c : Color} {p : Position} (hp : p.turn = c) :
    ¬ ForcesMate c 0 p := by
  intro h
  generalize hn : (0 : Nat) = n at h
  induction h with
  | mated _ _ h' _ => exact Color.other_ne c (h'.symm.trans hp)
  | attack => omega
  | defend _ _ h' _ _ _ => exact Color.other_ne c (h'.symm.trans hp)

/-- **Monotonicity**: a forced mate within `n` moves is a forced mate within `n + k` moves. -/
theorem ForcesMate.mono {c : Color} {n : Nat} {p : Position} (h : ForcesMate c n p) (k : Nat) :
    ForcesMate c (n + k) p := by
  induction h with
  | mated n p h₁ h₂ => exact .mated _ p h₁ h₂
  | attack n p m h₁ h₂ _ ih =>
    rw [Nat.add_right_comm]
    exact .attack _ p m h₁ h₂ ih
  | defend n p h₁ h₂ _ ih => exact .defend _ p h₁ h₂ ih

/-- A forced mate reaches a checkmate by a sequence of legal moves. -/
theorem ForcesMate.exists_checkmate {c : Color} {n : Nat} {p : Position} (h : ForcesMate c n p) :
    ∃ ms q, playLegal p ms = some q ∧ isCheckmate q = true := by
  induction h with
  | mated n p _ h => exact ⟨[], p, rfl, h⟩
  | attack n p m _ hm _ ih =>
    obtain ⟨ms, q, hq, hc⟩ := ih
    refine ⟨m :: ms, q, ?_, hc⟩
    simp [playLegal, (isLegal_iff p m).2 hm, hq]
  | defend n p _ hne _ ih =>
    obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨ms, q, hq, hc⟩ := ih m hm
    refine ⟨m :: ms, q, ?_, hc⟩
    simp [playLegal, (isLegal_iff p m).2 hm, hq]

/-- **The dead-position rule never interrupts a forced mate**: a position from which a mate can
be forced is not dead. -/
theorem ForcesMate.not_isDead {c : Color} {n : Nat} {p : Position} (h : ForcesMate c n p) :
    ¬ IsDead p := by
  intro hd
  obtain ⟨ms, q, hq, hc⟩ := h.exists_checkmate
  rw [hd ms q hq] at hc
  exact Bool.false_ne_true hc

end LeanTheory.Chess
