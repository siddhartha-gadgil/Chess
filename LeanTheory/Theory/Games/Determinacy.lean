/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import Mathlib.Order.MinMax
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.List.Basic

/-!
# Zermelo determinacy for finite-depth two-player games

An abstract, chess-independent formalization of backward induction (note `N-04`, abstract part).

* `Player`: the two players; `first` maximizes the outcome, `second` minimizes it;
* `Game S α`: states `S`, player to move, finite list of successor states (empty = terminal),
  terminal outcome in a linear order `α` (from the first player's point of view), and a
  depth bound `bound` strictly decreasing along moves;
* `Game.value`: the minimax value, by backward induction;
* `Game.Strategy`, `Game.play`: positional strategies (a state may carry the whole history) and
  the outcome when both players follow given strategies;
* `Game.optimal`: one positional strategy that is optimal for both players;
* `Game.value_le_play_optimal`, `Game.play_optimal_le_value`: each player guarantees the value;
* `Game.maxForces_iff`, `Game.minForces_iff`: the value is the best bound either player can
  force, hence unique;
* `Game.GuaranteesGe`, `Game.GuaranteesLe`: AND–OR (game-tree) forms of "can force", with
  `Game.guaranteesGe_iff`, `Game.guaranteesLe_iff`;
* `Outcome`, `Game.exactly_one_outcome`: for outcomes `blackWins < draw < whiteWins`, exactly one
  of "first forces a win", "second forces a win", "both force at least a draw" holds.

A sanity section checks the terminal case, a subtraction game (take 1 or 2 stones; the player
unable to move loses) whose values are computed for all positions, and that a one-state loop
admits no depth bound.

Scope: this file asserts nothing about chess; the chess instance needs a proved bound on game
length (75-move rule) and is a separate file.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.Games

/-- The two players. The `first` player maximizes the outcome, the `second` minimizes it. -/
inductive Player where
  /-- The maximizing player (White in chess). -/
  | first
  /-- The minimizing player (Black in chess). -/
  | second
  deriving DecidableEq, Repr

variable {α : Type*} [LinearOrder α]

/-- The best value among `v :: vs` for player `p`: the maximum for `first`, the minimum for
`second`. -/
def Player.best : Player → α → List α → α
  | .first, v, vs => vs.foldr max v
  | .second, v, vs => vs.foldr min v

/-- Value of a node with child values `l` and terminal outcome `o`: `o` if there are no
children, otherwise the best child value for player `p`. -/
def Player.combine (p : Player) (o : α) : List α → α
  | [] => o
  | v :: vs => p.best v vs

/-- The best value is one of the candidates. -/
theorem Player.best_mem (p : Player) (v : α) (vs : List α) : p.best v vs ∈ v :: vs := by
  cases p <;> induction vs with
  | nil => simp [Player.best]
  | cons w ws ih =>
    simp only [Player.best, List.foldr_cons, List.mem_cons] at ih ⊢
    first
    | rcases max_choice w (ws.foldr max v) with h | h <;> rw [h] <;> grind
    | rcases min_choice w (ws.foldr min v) with h | h <;> rw [h] <;> grind

/-- For the first player, every candidate is at most the best value. -/
theorem Player.le_best_first {v x : α} {vs : List α} (hx : x ∈ v :: vs) :
    x ≤ Player.first.best v vs := by
  induction vs with
  | nil => simp_all [Player.best]
  | cons w ws ih =>
    simp only [Player.best, List.foldr_cons, List.mem_cons] at ih hx ⊢
    rcases hx with rfl | rfl | hx
    · exact le_trans (ih (by simp)) (le_max_right _ _)
    · exact le_max_left _ _
    · exact le_trans (ih (by simp [hx])) (le_max_right _ _)

/-- For the second player, the best value is at most every candidate. -/
theorem Player.best_second_le {v x : α} {vs : List α} (hx : x ∈ v :: vs) :
    Player.second.best v vs ≤ x := by
  induction vs with
  | nil => simp_all [Player.best]
  | cons w ws ih =>
    simp only [Player.best, List.foldr_cons, List.mem_cons] at ih hx ⊢
    rcases hx with rfl | rfl | hx
    · exact le_trans (min_le_right _ _) (ih (by simp))
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (ih (by simp [hx]))

/-- A two-player game of bounded depth on states `S` with outcomes in the linear order `α`
(from the first player's point of view). States may carry arbitrary history. -/
structure Game (S : Type*) (α : Type*) [LinearOrder α] where
  /-- The player to move at a state. -/
  toMove : S → Player
  /-- The successor states; the empty list means the state is terminal. -/
  moves : S → List S
  /-- The outcome at a state (only used at terminal states). -/
  outcome : S → α
  /-- A bound on the remaining depth of the game. -/
  bound : S → ℕ
  /-- The depth bound decreases strictly along every move. -/
  bound_lt : ∀ s t, t ∈ moves s → bound t < bound s

namespace Game

variable {S : Type*} (g : Game S α)

/-- Well-founded induction along moves: to prove `motive s`, one may assume `motive t` for every
successor `t` of `s`. -/
theorem induction_on {motive : S → Prop} (s : S)
    (ih : ∀ s, (∀ t ∈ g.moves s, motive t) → motive s) : motive s :=
  ih s fun t _ => induction_on t ih
termination_by g.bound s
decreasing_by exact g.bound_lt _ _ ‹_›

/-- The minimax value by backward induction: the outcome at terminal states, otherwise the
maximum (first player to move) or minimum (second player to move) over successors. -/
def value (s : S) : α :=
  (g.toMove s).combine (g.outcome s) ((g.moves s).attach.map fun t => value t.1)
termination_by g.bound s
decreasing_by exact g.bound_lt _ _ t.2

/-- Unfolding equation for `value`. -/
theorem value_eq (s : S) :
    g.value s = (g.toMove s).combine (g.outcome s) ((g.moves s).map g.value) := by
  rw [value]
  congr 1
  exact List.attach_map_val

/-- At a terminal state the value is the outcome. -/
theorem value_of_terminal {s : S} (h : g.moves s = []) : g.value s = g.outcome s := by
  rw [value_eq, h]
  rfl

/-- At a nonterminal state the value is attained by some move. -/
theorem exists_mem_value_eq {s : S} (h : g.moves s ≠ []) :
    ∃ t ∈ g.moves s, g.value t = g.value s := by
  obtain ⟨t, ts, hts⟩ := List.exists_cons_of_ne_nil h
  have hm := (g.toMove s).best_mem (g.value t) (ts.map g.value)
  rw [← List.map_cons, ← hts, List.mem_map] at hm
  obtain ⟨u, hu, hv⟩ := hm
  refine ⟨u, hu, ?_⟩
  rw [hv, value_eq g s, hts]
  rfl

/-- When the first player moves, the value is at least the value of every successor. -/
theorem value_le_of_first {s t : S} (hp : g.toMove s = .first) (ht : t ∈ g.moves s) :
    g.value t ≤ g.value s := by
  obtain ⟨u, us, hus⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem ht)
  rw [value_eq g s, hp, hus]
  apply Player.le_best_first
  rw [← List.map_cons, ← hus]
  exact List.mem_map_of_mem ht

/-- When the second player moves, the value is at most the value of every successor. -/
theorem le_value_of_second {s t : S} (hp : g.toMove s = .second) (ht : t ∈ g.moves s) :
    g.value s ≤ g.value t := by
  obtain ⟨u, us, hus⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem ht)
  rw [value_eq g s, hp, hus]
  apply Player.best_second_le
  rw [← List.map_cons, ← hus]
  exact List.mem_map_of_mem ht

/-- A positional strategy: a choice of legal successor at every nonterminal state. It is used by
a player only at states where that player is to move. Since states may carry history, this
covers history-dependent strategies. -/
structure Strategy where
  /-- The chosen successor. -/
  next : S → S
  /-- The choice is a legal move at every nonterminal state. -/
  next_mem : ∀ s, g.moves s ≠ [] → next s ∈ g.moves s

/-- The outcome of the play from `s` when the first player follows `σ` and the second
follows `τ`. -/
def play (σ τ : g.Strategy) (s : S) : α :=
  if _h : g.moves s = [] then g.outcome s
  else
    match g.toMove s with
    | .first => play σ τ (σ.next s)
    | .second => play σ τ (τ.next s)
termination_by g.bound s
decreasing_by
  · exact g.bound_lt _ _ (σ.next_mem s ‹_›)
  · exact g.bound_lt _ _ (τ.next_mem s ‹_›)

/-- The play from a terminal state ends with its outcome. -/
theorem play_of_terminal (σ τ : g.Strategy) {s : S} (h : g.moves s = []) :
    g.play σ τ s = g.outcome s := by
  rw [play]
  simp [h]

/-- When the first player is to move, the play continues from `σ.next s`. -/
theorem play_of_first (σ τ : g.Strategy) {s : S} (h : g.moves s ≠ [])
    (hp : g.toMove s = .first) : g.play σ τ s = g.play σ τ (σ.next s) := by
  rw [play]
  simp only [h, dite_false]
  split <;> simp_all

/-- When the second player is to move, the play continues from `τ.next s`. -/
theorem play_of_second (σ τ : g.Strategy) {s : S} (h : g.moves s ≠ [])
    (hp : g.toMove s = .second) : g.play σ τ s = g.play σ τ (τ.next s) := by
  rw [play]
  simp only [h, dite_false]
  split <;> simp_all

/-- The optimal strategy: always move to a successor with the same value. It is optimal for
whichever player is to move. -/
def optimal : g.Strategy where
  next s := if h : g.moves s = [] then s else (g.exists_mem_value_eq h).choose
  next_mem s h := by
    simp only [h, dite_false]
    exact (g.exists_mem_value_eq h).choose_spec.1

/-- The optimal strategy preserves the value. -/
theorem value_optimal_next {s : S} (h : g.moves s ≠ []) :
    g.value (g.optimal.next s) = g.value s := by
  change g.value (if h : g.moves s = [] then s else (g.exists_mem_value_eq h).choose) = _
  simp only [h, dite_false]
  exact (g.exists_mem_value_eq h).choose_spec.2

/-- **Zermelo, first player**: following `optimal`, the first player obtains at least the value
against every strategy of the second player. -/
theorem value_le_play_optimal (τ : g.Strategy) (s : S) :
    g.value s ≤ g.play g.optimal τ s := by
  induction s using g.induction_on with
  | ih s ih =>
    by_cases h : g.moves s = []
    · rw [play_of_terminal _ _ _ h, value_of_terminal _ h]
    · cases hp : g.toMove s
      · rw [play_of_first _ _ _ h hp, ← g.value_optimal_next h]
        exact ih _ (g.optimal.next_mem s h)
      · rw [play_of_second _ _ _ h hp]
        exact le_trans (g.le_value_of_second hp (τ.next_mem s h)) (ih _ (τ.next_mem s h))

/-- **Zermelo, second player**: following `optimal`, the second player concedes at most the
value against every strategy of the first player. -/
theorem play_optimal_le_value (σ : g.Strategy) (s : S) :
    g.play σ g.optimal s ≤ g.value s := by
  induction s using g.induction_on with
  | ih s ih =>
    by_cases h : g.moves s = []
    · rw [play_of_terminal _ _ _ h, value_of_terminal _ h]
    · cases hp : g.toMove s
      · rw [play_of_first _ _ _ h hp]
        exact le_trans (ih _ (σ.next_mem s h)) (g.value_le_of_first hp (σ.next_mem s h))
      · rw [play_of_second _ _ _ h hp, ← g.value_optimal_next h]
        exact ih _ (g.optimal.next_mem s h)

/-- The first player can force an outcome `≥ v` from `s`. -/
def MaxForces (v : α) (s : S) : Prop :=
  ∃ σ : g.Strategy, ∀ τ : g.Strategy, v ≤ g.play σ τ s

/-- The second player can force an outcome `≤ v` from `s`. -/
def MinForces (v : α) (s : S) : Prop :=
  ∃ τ : g.Strategy, ∀ σ : g.Strategy, g.play σ τ s ≤ v

/-- The first player can force `≥ v` exactly when `v ≤ value s`; in particular no strategy
guarantees more than the value. -/
theorem maxForces_iff (v : α) (s : S) : g.MaxForces v s ↔ v ≤ g.value s :=
  ⟨fun ⟨σ, hσ⟩ => le_trans (hσ g.optimal) (g.play_optimal_le_value σ s),
    fun h => ⟨g.optimal, fun τ => le_trans h (g.value_le_play_optimal τ s)⟩⟩

/-- The second player can force `≤ v` exactly when `value s ≤ v`. -/
theorem minForces_iff (v : α) (s : S) : g.MinForces v s ↔ g.value s ≤ v :=
  ⟨fun ⟨τ, hτ⟩ => le_trans (g.value_le_play_optimal τ s) (hτ g.optimal),
    fun h => ⟨g.optimal, fun σ => le_trans (g.play_optimal_le_value σ s) h⟩⟩

/-- **Uniqueness of the value**: if the first player can force `≥ v` and the second can force
`≤ v`, then `v` is the value. -/
theorem eq_value_of_forces {v : α} {s : S} (h₁ : g.MaxForces v s) (h₂ : g.MinForces v s) :
    v = g.value s :=
  le_antisymm ((g.maxForces_iff v s).1 h₁) ((g.minForces_iff v s).1 h₂)

/-- The value is forced by both players. -/
theorem forces_value (s : S) : g.MaxForces (g.value s) s ∧ g.MinForces (g.value s) s :=
  ⟨(g.maxForces_iff _ s).2 le_rfl, (g.minForces_iff _ s).2 le_rfl⟩

/-- AND–OR form of "the first player guarantees `≥ v` from `s`": at terminal states the outcome
is `≥ v`; if the first player moves, some successor works; if the second player moves, every
successor works. -/
inductive GuaranteesGe (v : α) : S → Prop where
  /-- A terminal state with outcome `≥ v`. -/
  | terminal (s : S) : g.moves s = [] → v ≤ g.outcome s → GuaranteesGe v s
  /-- The first player moves to a successor from which it guarantees `≥ v`. -/
  | first (s t : S) : g.toMove s = .first → t ∈ g.moves s → GuaranteesGe v t →
      GuaranteesGe v s
  /-- The second player moves, and every successor guarantees `≥ v`. -/
  | second (s : S) : g.moves s ≠ [] → g.toMove s = .second →
      (∀ t ∈ g.moves s, GuaranteesGe v t) → GuaranteesGe v s

/-- AND–OR form of "the second player guarantees `≤ v` from `s`". -/
inductive GuaranteesLe (v : α) : S → Prop where
  /-- A terminal state with outcome `≤ v`. -/
  | terminal (s : S) : g.moves s = [] → g.outcome s ≤ v → GuaranteesLe v s
  /-- The first player moves, and every successor guarantees `≤ v`. -/
  | first (s : S) : g.moves s ≠ [] → g.toMove s = .first →
      (∀ t ∈ g.moves s, GuaranteesLe v t) → GuaranteesLe v s
  /-- The second player moves to a successor from which it guarantees `≤ v`. -/
  | second (s t : S) : g.toMove s = .second → t ∈ g.moves s → GuaranteesLe v t →
      GuaranteesLe v s

/-- The AND–OR guarantee for the first player holds exactly when `v ≤ value s`. -/
theorem guaranteesGe_iff (v : α) (s : S) : g.GuaranteesGe v s ↔ v ≤ g.value s := by
  constructor
  · intro h
    induction h with
    | terminal s hs hv => rwa [value_of_terminal _ hs]
    | first s t hp ht _ ih => exact le_trans ih (g.value_le_of_first hp ht)
    | second s hs _ _ ih =>
      obtain ⟨t, ht, hv⟩ := g.exists_mem_value_eq hs
      rw [← hv]
      exact ih t ht
  · induction s using g.induction_on with
    | ih s ih =>
      intro hv
      by_cases hs : g.moves s = []
      · exact .terminal s hs (by rwa [value_of_terminal _ hs] at hv)
      · cases hp : g.toMove s
        · obtain ⟨t, ht, htv⟩ := g.exists_mem_value_eq hs
          exact .first s t hp ht (ih t ht (htv ▸ hv))
        · exact .second s hs hp fun t ht =>
            ih t ht (le_trans hv (g.le_value_of_second hp ht))

/-- The AND–OR guarantee for the second player holds exactly when `value s ≤ v`. -/
theorem guaranteesLe_iff (v : α) (s : S) : g.GuaranteesLe v s ↔ g.value s ≤ v := by
  constructor
  · intro h
    induction h with
    | terminal s hs hv => rwa [value_of_terminal _ hs]
    | first s hs _ _ ih =>
      obtain ⟨t, ht, hv⟩ := g.exists_mem_value_eq hs
      rw [← hv]
      exact ih t ht
    | second s t hp ht _ ih => exact le_trans (g.le_value_of_second hp ht) ih
  · induction s using g.induction_on with
    | ih s ih =>
      intro hv
      by_cases hs : g.moves s = []
      · exact .terminal s hs (by rwa [value_of_terminal _ hs] at hv)
      · cases hp : g.toMove s
        · exact .first s hs hp fun t ht =>
            ih t ht (le_trans (g.value_le_of_first hp ht) hv)
        · obtain ⟨t, ht, htv⟩ := g.exists_mem_value_eq hs
          exact .second s t hp ht (ih t ht (htv ▸ hv))

end Game

/-- Three-valued outcomes from the first player's (White's) point of view. -/
inductive Outcome where
  /-- The second player (Black) wins. -/
  | blackWins
  /-- Draw. -/
  | draw
  /-- The first player (White) wins. -/
  | whiteWins
  deriving DecidableEq, Repr

namespace Outcome

/-- Encoding `blackWins ↦ 0`, `draw ↦ 1`, `whiteWins ↦ 2`, used to order outcomes. -/
def toNat : Outcome → ℕ
  | blackWins => 0
  | draw => 1
  | whiteWins => 2

/-- The encoding is injective. -/
theorem toNat_injective : Function.Injective toNat := by
  intro a b h
  cases a <;> cases b <;> simp_all [toNat]

/-- Outcomes are linearly ordered by `blackWins < draw < whiteWins`. -/
instance : LinearOrder Outcome := LinearOrder.lift' toNat toNat_injective

/-- The order on outcomes is the order of their encodings. -/
theorem le_iff_toNat {a b : Outcome} : a ≤ b ↔ a.toNat ≤ b.toNat := Iff.rfl

/-- `blackWins ≤ draw`. -/
@[simp] theorem blackWins_le_draw : blackWins ≤ draw := le_iff_toNat.2 (by simp [toNat])

/-- `draw ≤ whiteWins`. -/
@[simp] theorem draw_le_whiteWins : draw ≤ whiteWins := le_iff_toNat.2 (by simp [toNat])

/-- `blackWins ≤ whiteWins`. -/
@[simp] theorem blackWins_le_whiteWins : blackWins ≤ whiteWins :=
  le_iff_toNat.2 (by simp [toNat])

end Outcome

namespace Game

variable {S : Type*} (g : Game S Outcome)

/-- **Zermelo trichotomy**: from every state exactly one holds: the first player can force a
win, the second player can force a win, or both players can force at least a draw. -/
theorem exactly_one_outcome (s : S) :
    (g.MaxForces .whiteWins s ∧ ¬ g.MinForces .blackWins s ∧
        ¬ (g.MaxForces .draw s ∧ g.MinForces .draw s)) ∨
      (¬ g.MaxForces .whiteWins s ∧ g.MinForces .blackWins s ∧
        ¬ (g.MaxForces .draw s ∧ g.MinForces .draw s)) ∨
      (¬ g.MaxForces .whiteWins s ∧ ¬ g.MinForces .blackWins s ∧
        (g.MaxForces .draw s ∧ g.MinForces .draw s)) := by
  simp only [maxForces_iff, minForces_iff, Outcome.le_iff_toNat]
  cases g.value s <;> simp [Outcome.toNat]

/-- The first player can force a win exactly when the value is `whiteWins`. -/
theorem maxForces_whiteWins_iff (s : S) :
    g.MaxForces .whiteWins s ↔ g.value s = .whiteWins := by
  rw [maxForces_iff, Outcome.le_iff_toNat]
  cases g.value s <;> simp [Outcome.toNat]

/-- The second player can force a win exactly when the value is `blackWins`. -/
theorem minForces_blackWins_iff (s : S) :
    g.MinForces .blackWins s ↔ g.value s = .blackWins := by
  rw [minForces_iff, Outcome.le_iff_toNat]
  cases g.value s <;> simp [Outcome.toNat]

end Game

/-! ## Sanity checks -/

section Sanity

/-- Degenerate case: at a terminal state the value is the outcome and every play ends there. -/
theorem Game.sanity_terminal {S : Type*} (g : Game S α) {s : S} (h : g.moves s = [])
    (σ τ : g.Strategy) : g.value s = g.outcome s ∧ g.play σ τ s = g.outcome s :=
  ⟨g.value_of_terminal h, g.play_of_terminal σ τ h⟩

/-- The other player. -/
def Player.other : Player → Player
  | .first => .second
  | .second => .first

/-- Successors in the subtraction game: from `n` stones take 1 or 2; the other player moves. -/
def subtractionMoves : ℕ × Player → List (ℕ × Player)
  | (0, _) => []
  | (1, p) => [(0, p.other)]
  | (n + 2, p) => [(n + 1, p.other), (n, p.other)]

/-- The subtraction game: take 1 or 2 stones; the player unable to move (no stones) loses. -/
def subtractionGame : Game (ℕ × Player) Outcome where
  toMove s := s.2
  moves := subtractionMoves
  outcome s := if s.2 = .first then .blackWins else .whiteWins
  bound s := s.1
  bound_lt s t ht := by
    match s, ht with
    | (1, p), ht => simp_all [subtractionMoves]
    | (n + 2, p), ht =>
      simp only [subtractionMoves, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> simp

/-- Value of the subtraction game: the player to move loses exactly when the number of stones
is divisible by 3. -/
theorem subtractionGame_value (n : ℕ) :
    subtractionGame.value (n, .first) =
        (if n % 3 = 0 then .blackWins else .whiteWins) ∧
      subtractionGame.value (n, .second) =
        (if n % 3 = 0 then .whiteWins else .blackWins) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      refine ⟨?_, ?_⟩ <;> rw [Game.value_of_terminal _ rfl] <;> rfl
    | 1 =>
      have h0 := ih 0 (by omega)
      simp only [Nat.zero_mod, ↓reduceIte] at h0
      simp only [Nat.reduceMod, Nat.one_ne_zero, ↓reduceIte]
      refine ⟨?_, ?_⟩
      · rw [Game.value_eq]
        exact h0.2
      · rw [Game.value_eq]
        exact h0.1
    | m + 2 =>
      have h1 := ih (m + 1) (by omega)
      have h0 := ih m (by omega)
      have e1 : subtractionGame.value (m + 2, .first) =
          max (subtractionGame.value (m, .second)) (subtractionGame.value (m + 1, .second)) := by
        rw [Game.value_eq]
        rfl
      have e2 : subtractionGame.value (m + 2, .second) =
          min (subtractionGame.value (m, .first)) (subtractionGame.value (m + 1, .first)) := by
        rw [Game.value_eq]
        rfl
      rw [e1, e2, h0.1, h0.2, h1.1, h1.2]
      obtain h | h | h : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
      · have a1 : (m + 1) % 3 = 1 := by omega
        have a2 : (m + 2) % 3 = 2 := by omega
        simp [h, a1, a2]
      · have a1 : (m + 1) % 3 = 2 := by omega
        have a2 : (m + 2) % 3 = 0 := by omega
        simp [h, a1, a2]
      · have a1 : (m + 1) % 3 = 0 := by omega
        have a2 : (m + 2) % 3 = 1 := by omega
        simp [h, a1, a2]

/-- Concrete instance: with 3 stones the first player to move loses (the second forces a
win); with 4 stones the first player forces a win. -/
theorem subtractionGame_three_four :
    subtractionGame.MinForces .blackWins (3, .first) ∧
      subtractionGame.MaxForces .whiteWins (4, .first) := by
  rw [Game.minForces_blackWins_iff, Game.maxForces_whiteWins_iff]
  exact ⟨by simpa using (subtractionGame_value 3).1, by simpa using (subtractionGame_value 4).1⟩

/-- The depth bound is a genuine hypothesis: a state that is its own successor admits no depth
function decreasing along moves, so it cannot be made into a `Game`. -/
theorem no_bound_for_loop {S : Type*} (s : S) (bound : S → ℕ) :
    ¬ ∀ a b, b ∈ (fun _ => [s] : S → List S) a → bound b < bound a :=
  fun h => Nat.lt_irrefl _ (h s s (List.mem_singleton_self s))

end Sanity

end LeanTheory.Games
