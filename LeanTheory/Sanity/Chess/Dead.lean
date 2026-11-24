/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Sanity.Chess.Rules
public import LeanTheory.Kernel.Chess.Game

/-!
# Sanity: the initial position is not dead

Guards the semantic definition `IsDead` (FIDE 5.2.2, `Kernel/Chess/Game`) against vacuity in the
other direction from `dead_KK`: the initial position is not dead, because Fool's mate is a legal
sequence ending in checkmate (`foolsMate_checkmate`).
-/

@[expose] public section

namespace LeanTheory.Sanity.Chess

open LeanTheory.Chess

/-- A position from which some legal sequence reaches checkmate is not dead. -/
theorem not_isDead_of_reaches {p : Position} {ms : List Move}
    (h : (playLegal p ms).map isCheckmate = some true) : ¬ IsDead p := by
  intro hd
  cases hq : playLegal p ms with
  | none => rw [hq] at h; simp at h
  | some q =>
    rw [hq] at h
    simp only [Option.map_some, Option.some.injEq] at h
    rw [hd ms q hq] at h
    exact Bool.false_ne_true h

/-- **The initial position is not dead.** -/
theorem initial_not_dead : ¬ IsDead initialPosition :=
  not_isDead_of_reaches foolsMate_checkmate

end LeanTheory.Sanity.Chess
