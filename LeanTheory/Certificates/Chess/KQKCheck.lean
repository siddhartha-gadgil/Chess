/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.Chess.Game

/-!
# Certificate checker for king and queen versus king

Infrastructure for goal `G-2` (note `N-05`, route (b)). A *KQK table* assigns to each triple of
squares `(wk, wq, bk)` (white king, white queen, black king; index `i = 4096 wk + 64 wq + bk`) an
entry encoding a depth `d ≤ 10` and a White move. The table is produced by an untrusted program
(`N-06`); this file defines a Boolean checker `stateOK` for one entry and proves it sound:

* `kqkBoard`, `kqkPos`: the position with the three pieces, side to move `t`, halfmove clock `h`,
  no castling rights and no en passant target;
* `play_kqk_king`, `play_kqk_queen`, `play_kqk_black`: a non-capturing one-step king move or a
  non-capturing queen move from a `kqkPos` gives the `kqkPos` with the piece moved (symbolic
  lemmas, so the checker never evaluates boards built by `play`);
* `ForcesMate.kqk_halfmove`: forced mates do not depend on the halfmove clock;
* `table_sound`: if `stateOK T i = true` for every index `i`, then every entry with depth
  `d ≠ 0` is a forced mate for White within `d` moves.

The checker evaluates only `kqkPos` positions: the legality of White's move (via the queen's or
king's own move list and a check test), checkmate of Black, and for each legal Black reply that
it is a king step that does not capture, landing on an entry of smaller nonzero depth.
-/

@[expose] public section

namespace LeanTheory.Chess

/-! ### KQK positions -/

/-- The board with a white king on `wk`, a white queen on `wq` and a black king on `bk` (the first
listed piece wins if squares coincide). -/
def kqkBoard (wk wq bk : Square) : Board := fun s =>
  if s = wk then some ⟨.white, .king⟩
  else if s = wq then some ⟨.white, .queen⟩
  else if s = bk then some ⟨.black, .king⟩
  else none

/-- The KQK position with side to move `t` and halfmove clock `h`, no castling rights and no en
passant target. -/
def kqkPos (wk wq bk : Square) (t : Color) (h : Nat) : Position :=
  ⟨kqkBoard wk wq bk, t, .none, none, h⟩

/-- The square with index `n mod 64`. -/
def sqOf (n : Nat) : Square := ⟨n % 64, Nat.mod_lt _ (by omega)⟩

/-! ### Moves from KQK positions (symbolic lemmas) -/

/-- A non-capturing white king move, not two squares sideways, from a KQK position. -/
theorem play_kqk_king (wk wq bk dst : Square) (t : Nat) (h₁ : wk ≠ wq) (h₂ : wk ≠ bk)
    (hd₀ : dst ≠ wk) (hd₁ : dst ≠ wq) (hd₂ : dst ≠ bk) (hd₃ : dst.val ≠ wk.val + 2)
    (hd₄ : wk.val ≠ dst.val + 2) :
    play (kqkPos wk wq bk .white t) ⟨wk, dst, none⟩ = kqkPos dst wq bk .black (t + 1) := by
  simp only [play, kqkPos, kqkBoard]
  simp only [↓reduceIte, BEq.rfl, Bool.true_and, beq_iff_eq, hd₃, hd₄, Option.some_beq_some,
    Option.none_beq_some, Bool.and_false, hd₀, hd₁, hd₂, Option.isNone_none, Bool.and_true,
    Bool.false_and, Bool.false_eq_true, Color.other, CastlingRights.update, CastlingRights.none,
    Bool.not_or, Bool.and_eq_true, Piece.mk.injEq, reduceCtorEq, and_false, Bool.or_eq_true,
    false_and, Option.isSome_none, Bool.or_false, Position.mk.injEq,
    and_self, and_true]
  funext s
  unfold kqkBoard
  by_cases a : s = dst <;> by_cases b : s = wk <;> simp_all

/-- A non-capturing queen move from a KQK position. -/
theorem play_kqk_queen (wk wq bk dst : Square) (t : Nat) (h₁ : wk ≠ wq) (h₂ : wq ≠ bk)
    (hd₀ : dst ≠ wk) (hd₁ : dst ≠ wq) (hd₂ : dst ≠ bk) :
    play (kqkPos wk wq bk .white t) ⟨wq, dst, none⟩ = kqkPos wk dst bk .black (t + 1) := by
  simp only [play, kqkPos, kqkBoard]
  simp only [h₁.symm, ↓reduceIte, Option.some_beq_some, Bool.and_eq_true, beq_iff_eq,
    Piece.mk.injEq, reduceCtorEq, and_false, false_and, Option.none_beq_some, Bool.and_false, hd₀,
    hd₁, hd₂, Option.isNone_none, Bool.and_true, Bool.false_and, Bool.false_eq_true, Color.other,
    CastlingRights.update, CastlingRights.none, Bool.not_or, Bool.or_eq_true, Option.isSome_none,
    Bool.or_false, Position.mk.injEq, and_self, and_true]
  have h₁' := Ne.symm h₁
  funext s
  unfold kqkBoard
  by_cases a : s = dst <;> by_cases b : s = wq <;> simp_all

/-- A non-capturing black king move, not two squares sideways, from a KQK position. -/
theorem play_kqk_black (wk wq bk dst : Square) (t : Nat) (h₁ : bk ≠ wk) (h₂ : bk ≠ wq)
    (hd₀ : dst ≠ wk) (hd₁ : dst ≠ wq) (hd₂ : dst ≠ bk) (hd₃ : dst.val ≠ bk.val + 2)
    (hd₄ : bk.val ≠ dst.val + 2) :
    play (kqkPos wk wq bk .black t) ⟨bk, dst, none⟩ = kqkPos wk wq dst .white (t + 1) := by
  simp only [play, kqkPos, kqkBoard]
  simp only [h₁, ↓reduceIte, h₂, BEq.rfl, Bool.true_and, beq_iff_eq, hd₃, hd₄,
    Option.some_beq_some, Option.none_beq_some, Bool.and_false, hd₀, hd₁, hd₂, Option.isNone_none,
    Bool.and_true, Bool.false_and, Bool.false_eq_true, Color.other, CastlingRights.update,
    CastlingRights.none, Bool.not_or, Bool.and_eq_true, Piece.mk.injEq, reduceCtorEq, and_false,
    Bool.or_eq_true, false_and, Option.isSome_none, Bool.or_false, Position.mk.injEq,
    and_self, and_true]
  funext s
  unfold kqkBoard
  by_cases a : s = dst <;> by_cases b : s = bk <;> simp_all

/-- Legal moves do not depend on the halfmove clock. -/
theorem legalMoves_halfmove (p : Position) (h : Nat) :
    legalMoves { p with halfmove := h } = legalMoves p := rfl
/-- Checkmate does not depend on the halfmove clock. -/
theorem isCheckmate_halfmove (p : Position) (h : Nat) :
    isCheckmate { p with halfmove := h } = isCheckmate p := rfl
/-- Making a move commutes with changing the halfmove clock, up to the new clock. -/
theorem play_halfmove (p : Position) (h : Nat) (m : Move) :
    play { p with halfmove := h } m =
      { play p m with halfmove := (play { p with halfmove := h } m).halfmove } := rfl

/-! ### Halfmove clock and legal moves -/

/-- **Forced mates do not depend on the halfmove clock.** -/
theorem ForcesMate.halfmove {c : Color} {n : Nat} {p : Position} (hf : ForcesMate c n p) :
    ∀ k, ForcesMate c n { p with halfmove := k } := by
  induction hf with
  | mated n p h₁ h₂ => exact fun k => .mated n _ h₁ (by rw [isCheckmate_halfmove]; exact h₂)
  | attack n p m h₁ h₂ _ ih =>
    intro k
    refine .attack n _ m h₁ (by rw [legalMoves_halfmove]; exact h₂) ?_
    rw [play_halfmove]
    exact ih _
  | defend n p h₁ h₂ _ ih =>
    intro k
    refine .defend n _ h₁ (by rw [legalMoves_halfmove]; exact h₂) fun m hm => ?_
    rw [play_halfmove]
    exact ih m (by rw [legalMoves_halfmove] at hm; exact hm) _

/-- A move from the piece's own move list that does not leave the mover in check is legal. -/
theorem mem_legalMoves_of (p : Position) (s : Square) (k : PieceType) (m : Move)
    (hb : p.board s = some ⟨p.turn, k⟩) (hm : m ∈ pieceMoves p s k)
    (hc : inCheck (play p m).board p.turn = false) : m ∈ legalMoves p := by
  simp only [legalMoves, List.mem_filter, hc, Bool.not_false, and_true]
  refine List.mem_append_left _ (List.mem_flatMap.2 ⟨s, mem_allSquares s, ?_⟩)
  simp [hb, hm]

/-! ### The checker -/

/-- Index of the triple `(wk, wq, bk)`. -/
def kqkIdx (wk wq bk : Nat) : Nat := wk * 4096 + wq * 64 + bk

/-- The depth field (`0` = no claim) of a table entry. -/
def entDepth (e : Nat) : Nat := e % 16

/-- The source square field of a table entry. -/
def entSrc (e : Nat) : Nat := e / 16 % 64

/-- The destination square field of a table entry. -/
def entDst (e : Nat) : Nat := e / 1024 % 64

/-- A Black reply `m` in the KQK position `(wk, wq, bk)` is acceptable: it is a non-capturing
king step to a square whose table entry has a nonzero depth below `d`. -/
def replyOK (T : Nat → Nat) (d : Nat) (wk wq bk : Square) (m : Move) : Bool :=
  m.src == bk && m.promo == none && m.dst != wk && m.dst != wq && m.dst != bk &&
    m.dst.val != bk.val + 2 && bk.val != m.dst.val + 2 &&
    (0 < entDepth (T (kqkIdx wk.val wq.val m.dst.val)) &&
      entDepth (T (kqkIdx wk.val wq.val m.dst.val)) < d)

/-- After White's move to `(wk', wq', bk)`: White's king is not in check, and Black is either
checkmated or has legal moves, all acceptable for depth `d`. -/
def afterWhiteOK (T : Nat → Nat) (d : Nat) (wk' wq' bk : Square) : Bool :=
  !inCheck (kqkBoard wk' wq' bk) .white &&
    match legalMoves (kqkPos wk' wq' bk .black 0) with
    | [] => inCheck (kqkBoard wk' wq' bk) .black
    | m :: ms => (m :: ms).all (replyOK T d wk' wq' bk)

/-- The White move `src → dst` from `(wk, wq, bk)` is a king step or queen move in the piece's
move list, does not capture, and leads to a position accepted by `afterWhiteOK`. -/
def whiteOK (T : Nat → Nat) (d : Nat) (wk wq bk src dst : Square) : Bool :=
  (src == wk && dst != wk && dst != wq && dst != bk && dst.val != wk.val + 2 &&
      wk.val != dst.val + 2 &&
      (pieceMoves (kqkPos wk wq bk .white 0) wk .king).contains ⟨wk, dst, none⟩ &&
      afterWhiteOK T d dst wq bk) ||
    (src == wq && dst != wk && dst != wq && dst != bk &&
      (pieceMoves (kqkPos wk wq bk .white 0) wq .queen).contains ⟨wq, dst, none⟩ &&
      afterWhiteOK T d wk dst bk)

/-- **The check of one table entry** `i`: depth `0` (no claim), or depth `1 ≤ d ≤ 10`, three
distinct squares and an acceptable White move. -/
def stateOK (T : Nat → Nat) (i : Nat) : Bool :=
  entDepth (T i) == 0 ||
    (entDepth (T i) ≤ 10 && sqOf (i / 4096) != sqOf (i / 64) && sqOf (i / 4096) != sqOf i &&
      sqOf (i / 64) != sqOf i &&
      whiteOK T (entDepth (T i)) (sqOf (i / 4096)) (sqOf (i / 64)) (sqOf i)
        (sqOf (entSrc (T i))) (sqOf (entDst (T i))))

/-! ### Soundness -/

/-- Decoding the index of a triple of squares. -/
theorem sqOf_kqkIdx (wk wq bk : Square) :
    sqOf (kqkIdx wk.val wq.val bk.val / 4096) = wk ∧ sqOf (kqkIdx wk.val wq.val bk.val / 64) = wq ∧
      sqOf (kqkIdx wk.val wq.val bk.val) = bk := by
  have := wk.isLt; have := wq.isLt; have := bk.isLt
  refine ⟨Fin.ext ?_, Fin.ext ?_, Fin.ext ?_⟩ <;> simp only [sqOf, kqkIdx] <;> omega

/-- The position after an accepted White move and the forced mate from it. -/
theorem afterWhiteOK_sound (T : Nat → Nat) (d : Nat) (wk' wq' bk : Square)
    (hbk₁ : bk ≠ wk') (hbk₂ : bk ≠ wq')
    (ih : ∀ e < d + 1, ∀ wk wq bk : Square, entDepth (T (kqkIdx wk.val wq.val bk.val)) = e →
      e ≠ 0 → ∀ h, ForcesMate .white e (kqkPos wk wq bk .white h))
    (hok : afterWhiteOK T (d + 1) wk' wq' bk = true) (h : Nat) :
    ForcesMate .white d (kqkPos wk' wq' bk .black h) := by
  simp only [afterWhiteOK, Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨_, hok⟩ := hok
  have hlm : legalMoves (kqkPos wk' wq' bk .black h) = legalMoves (kqkPos wk' wq' bk .black 0) :=
    rfl
  split at hok
  · rename_i hnil
    refine .mated d _ rfl ?_
    simp only [isCheckmate, hlm, hnil, List.isEmpty_nil, Bool.and_true]
    exact hok
  · rename_i m₀ ms hcons
    have hne : legalMoves (kqkPos wk' wq' bk .black h) ≠ [] := by rw [hlm, hcons]; simp
    have hall : ∀ m ∈ legalMoves (kqkPos wk' wq' bk .black h),
        replyOK T (d + 1) wk' wq' bk m = true :=
      fun m hm => List.all_eq_true.1 hok m (by rw [← hcons, ← hlm]; exact hm)
    refine .defend d _ rfl hne fun m hm => ?_
    have hr := hall m hm
    simp only [replyOK, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at hr
    obtain ⟨⟨⟨⟨⟨⟨⟨hsrc, hpro⟩, hd₀⟩, hd₁⟩, hd₂⟩, hd₃⟩, hd₄⟩, hpos, hlt⟩ := hr
    have hm' : m = ⟨bk, m.dst, none⟩ := by cases m; simp_all
    rw [hm', play_kqk_black wk' wq' bk m.dst h hbk₁ hbk₂ hd₀ hd₁ hd₂ hd₃ hd₄]
    have := ih _ (by omega) wk' wq' m.dst rfl (by omega) (h + 1)
    have := this.mono (d - entDepth (T (kqkIdx wk'.val wq'.val m.dst.val)))
    rwa [show entDepth (T (kqkIdx wk'.val wq'.val m.dst.val)) +
      (d - entDepth (T (kqkIdx wk'.val wq'.val m.dst.val))) = d by omega] at this

/-- **Soundness of the KQK table check**: if every entry passes `stateOK`, then every entry of
nonzero depth `d` is a forced mate for White within `d` moves, for any halfmove clock. -/
theorem table_sound (T : Nat → Nat) (hT : ∀ i, i < 262144 → stateOK T i = true) :
    ∀ d, ∀ wk wq bk : Square, entDepth (T (kqkIdx wk.val wq.val bk.val)) = d → d ≠ 0 →
      ∀ h, ForcesMate .white d (kqkPos wk wq bk .white h) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro wk wq bk hd hd0 h
  have hi : kqkIdx wk.val wq.val bk.val < 262144 := by
    have := wk.isLt; have := wq.isLt; have := bk.isLt; simp only [kqkIdx]; omega
  have hs := hT _ hi
  obtain ⟨e₁, e₂, e₃⟩ := sqOf_kqkIdx wk wq bk
  simp only [stateOK, e₁, e₂, e₃, hd, Bool.or_eq_true, beq_iff_eq, hd0, false_or,
    Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hs
  obtain ⟨⟨⟨⟨_, h₁⟩, h₂⟩, h₃⟩, hw⟩ := hs
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have ih' : ∀ e < d' + 1, ∀ wk wq bk : Square, entDepth (T (kqkIdx wk.val wq.val bk.val)) = e →
      e ≠ 0 → ∀ h, ForcesMate .white e (kqkPos wk wq bk .white h) :=
    fun e he => ih e he
  generalize sqOf (entSrc (T (kqkIdx wk.val wq.val bk.val))) = src at hw
  generalize sqOf (entDst (T (kqkIdx wk.val wq.val bk.val))) = dst at hw
  simp only [whiteOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    List.contains_iff_mem] at hw
  rcases hw with ⟨⟨⟨⟨⟨⟨⟨_, hd₀⟩, hd₁⟩, hd₂⟩, hd₃⟩, hd₄⟩, hmem⟩, hok⟩ |
      ⟨⟨⟨⟨⟨_, hd₀⟩, hd₁⟩, hd₂⟩, hmem⟩, hok⟩
  · have hplay := play_kqk_king wk wq bk dst h h₁ h₂ hd₀ hd₁ hd₂ hd₃ hd₄
    have hc : inCheck (kqkBoard dst wq bk) .white = false := by
      have := hok
      simp only [afterWhiteOK, Bool.and_eq_true, Bool.not_eq_true'] at this
      exact this.1
    have hlegal : (⟨wk, dst, none⟩ : Move) ∈ legalMoves (kqkPos wk wq bk .white h) :=
      mem_legalMoves_of _ wk .king _ (by simp [kqkPos, kqkBoard]) hmem
        (by rw [hplay]; exact hc)
    refine .attack d' _ _ rfl hlegal ?_
    rw [hplay]
    exact afterWhiteOK_sound T d' dst wq bk (Ne.symm hd₂) (Ne.symm h₃) ih' hok (h + 1)
  · have hplay := play_kqk_queen wk wq bk dst h h₁ h₃ hd₀ hd₁ hd₂
    have hc : inCheck (kqkBoard wk dst bk) .white = false := by
      have := hok
      simp only [afterWhiteOK, Bool.and_eq_true, Bool.not_eq_true'] at this
      exact this.1
    have hlegal : (⟨wq, dst, none⟩ : Move) ∈ legalMoves (kqkPos wk wq bk .white h) :=
      mem_legalMoves_of _ wq .queen _ (by simp [kqkPos, kqkBoard, Ne.symm h₁]) hmem
        (by rw [hplay]; exact hc)
    refine .attack d' _ _ rfl hlegal ?_
    rw [hplay]
    exact afterWhiteOK_sound T d' wk dst bk (Ne.symm h₂) (Ne.symm hd₂) ih' hok (h + 1)

end LeanTheory.Chess
