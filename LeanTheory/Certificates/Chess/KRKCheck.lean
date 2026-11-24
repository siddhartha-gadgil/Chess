/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Certificates.Chess.KQKCheck

/-!
# Certificate checker for king and rook versus king

The rook analogue of `Certificates/Chess/KQKCheck` (goal `G-4`, note `N-10`): a *KRK table*
assigns to each triple `(wk, wr, bk)` (white king, white rook, black king; index
`kqkIdx wk wr bk = 4096 wk + 64 wr + bk`) an entry encoding a depth `d ≤ 16` (5 bits) and a White
move (`krkDepth`, `krkSrc`, `krkDst`: entry `= d + 32 src + 2048 dst`). The table comes from an
untrusted retrograde analysis; `krkStateOK` checks one entry and `krk_table_sound` proves the check
sound. The piece-independent lemmas (`sqOf`, `kqkIdx`, `sqOf_kqkIdx`, `ForcesMate.halfmove`,
`mem_legalMoves_of`, `legalMoves_halfmove`) are reused from `KQKCheck`. (In the code the rook's
square is still called `wq`.)
-/

@[expose] public section

namespace LeanTheory.Chess

/-! ### KRK positions -/

/-- The board with a white king on `wk`, a white rook on `wq` and a black king on `bk` (the first
listed piece wins if squares coincide). -/
def krkBoard (wk wq bk : Square) : Board := fun s =>
  if s = wk then some ⟨.white, .king⟩
  else if s = wq then some ⟨.white, .rook⟩
  else if s = bk then some ⟨.black, .king⟩
  else none

/-- The KRK position with side to move `t` and halfmove clock `h`, no castling rights and no en
passant target. -/
def krkPos (wk wq bk : Square) (t : Color) (h : Nat) : Position :=
  ⟨krkBoard wk wq bk, t, .none, none, h⟩

/-! ### Moves from KRK positions (symbolic lemmas) -/

/-- A non-capturing white king move, not two squares sideways, from a KRK position. -/
theorem play_krk_king (wk wq bk dst : Square) (t : Nat) (h₁ : wk ≠ wq) (h₂ : wk ≠ bk)
    (hd₀ : dst ≠ wk) (hd₁ : dst ≠ wq) (hd₂ : dst ≠ bk) (hd₃ : dst.val ≠ wk.val + 2)
    (hd₄ : wk.val ≠ dst.val + 2) :
    play (krkPos wk wq bk .white t) ⟨wk, dst, none⟩ = krkPos dst wq bk .black (t + 1) := by
  simp only [play, krkPos, krkBoard]
  simp only [↓reduceIte, BEq.rfl, Bool.true_and, beq_iff_eq, hd₃, hd₄, Option.some_beq_some,
    Option.none_beq_some, Bool.and_false, hd₀, hd₁, hd₂, Option.isNone_none, Bool.and_true,
    Bool.false_and, Bool.false_eq_true, Color.other, CastlingRights.update, CastlingRights.none,
    Bool.not_or, Bool.and_eq_true, Piece.mk.injEq, reduceCtorEq, and_false, Bool.or_eq_true,
    false_and, Option.isSome_none, Bool.or_false, Position.mk.injEq,
    and_self, and_true]
  funext s
  unfold krkBoard
  by_cases a : s = dst <;> by_cases b : s = wk <;> simp_all

/-- A non-capturing rook move from a KRK position. -/
theorem play_krk_rook (wk wq bk dst : Square) (t : Nat) (h₁ : wk ≠ wq) (h₂ : wq ≠ bk)
    (hd₀ : dst ≠ wk) (hd₁ : dst ≠ wq) (hd₂ : dst ≠ bk) :
    play (krkPos wk wq bk .white t) ⟨wq, dst, none⟩ = krkPos wk dst bk .black (t + 1) := by
  simp only [play, krkPos, krkBoard]
  simp only [h₁.symm, ↓reduceIte, Option.some_beq_some, Bool.and_eq_true, beq_iff_eq,
    Piece.mk.injEq, reduceCtorEq, and_false, false_and, Option.none_beq_some, Bool.and_false, hd₀,
    hd₁, hd₂, Option.isNone_none, Bool.and_true, Bool.false_and, Bool.false_eq_true, Color.other,
    CastlingRights.update, CastlingRights.none, Bool.not_or, Bool.or_eq_true, Option.isSome_none,
    Bool.or_false, Position.mk.injEq, and_self, and_true]
  have h₁' := Ne.symm h₁
  funext s
  unfold krkBoard
  by_cases a : s = dst <;> by_cases b : s = wq <;> simp_all

/-- A non-capturing black king move, not two squares sideways, from a KRK position. -/
theorem play_krk_black (wk wq bk dst : Square) (t : Nat) (h₁ : bk ≠ wk) (h₂ : bk ≠ wq)
    (hd₀ : dst ≠ wk) (hd₁ : dst ≠ wq) (hd₂ : dst ≠ bk) (hd₃ : dst.val ≠ bk.val + 2)
    (hd₄ : bk.val ≠ dst.val + 2) :
    play (krkPos wk wq bk .black t) ⟨bk, dst, none⟩ = krkPos wk wq dst .white (t + 1) := by
  simp only [play, krkPos, krkBoard]
  simp only [h₁, ↓reduceIte, h₂, BEq.rfl, Bool.true_and, beq_iff_eq, hd₃, hd₄,
    Option.some_beq_some, Option.none_beq_some, Bool.and_false, hd₀, hd₁, hd₂, Option.isNone_none,
    Bool.and_true, Bool.false_and, Bool.false_eq_true, Color.other, CastlingRights.update,
    CastlingRights.none, Bool.not_or, Bool.and_eq_true, Piece.mk.injEq, reduceCtorEq, and_false,
    Bool.or_eq_true, false_and, Option.isSome_none, Bool.or_false, Position.mk.injEq,
    and_self, and_true]
  funext s
  unfold krkBoard
  by_cases a : s = dst <;> by_cases b : s = bk <;> simp_all

/-! ### The checker -/

/-- The depth field (`0` = no claim) of a table entry. -/
def krkDepth (e : Nat) : Nat := e % 32

/-- The source square field of a table entry. -/
def krkSrc (e : Nat) : Nat := e / 32 % 64

/-- The destination square field of a table entry. -/
def krkDst (e : Nat) : Nat := e / 2048 % 64

/-- A Black reply `m` in the KRK position `(wk, wq, bk)` is acceptable: it is a non-capturing
king step to a square whose table entry has a nonzero depth below `d`. -/
def krkReplyOK (T : Nat → Nat) (d : Nat) (wk wq bk : Square) (m : Move) : Bool :=
  m.src == bk && m.promo == none && m.dst != wk && m.dst != wq && m.dst != bk &&
    m.dst.val != bk.val + 2 && bk.val != m.dst.val + 2 &&
    (0 < krkDepth (T (kqkIdx wk.val wq.val m.dst.val)) &&
      krkDepth (T (kqkIdx wk.val wq.val m.dst.val)) < d)

/-- After White's move to `(wk', wq', bk)`: White's king is not in check, and Black is either
checkmated or has legal moves, all acceptable for depth `d`. -/
def krkAfterWhiteOK (T : Nat → Nat) (d : Nat) (wk' wq' bk : Square) : Bool :=
  !inCheck (krkBoard wk' wq' bk) .white &&
    match legalMoves (krkPos wk' wq' bk .black 0) with
    | [] => inCheck (krkBoard wk' wq' bk) .black
    | m :: ms => (m :: ms).all (krkReplyOK T d wk' wq' bk)

/-- The White move `src → dst` from `(wk, wq, bk)` is a king step or rook move in the piece's
move list, does not capture, and leads to a position accepted by `krkAfterWhiteOK`. -/
def krkWhiteOK (T : Nat → Nat) (d : Nat) (wk wq bk src dst : Square) : Bool :=
  (src == wk && dst != wk && dst != wq && dst != bk && dst.val != wk.val + 2 &&
      wk.val != dst.val + 2 &&
      (pieceMoves (krkPos wk wq bk .white 0) wk .king).contains ⟨wk, dst, none⟩ &&
      krkAfterWhiteOK T d dst wq bk) ||
    (src == wq && dst != wk && dst != wq && dst != bk &&
      (pieceMoves (krkPos wk wq bk .white 0) wq .rook).contains ⟨wq, dst, none⟩ &&
      krkAfterWhiteOK T d wk dst bk)

/-- **The check of one table entry** `i`: depth `0` (no claim), or depth `1 ≤ d ≤ 16`, three
distinct squares and an acceptable White move. -/
def krkStateOK (T : Nat → Nat) (i : Nat) : Bool :=
  krkDepth (T i) == 0 ||
    (krkDepth (T i) ≤ 16 && sqOf (i / 4096) != sqOf (i / 64) && sqOf (i / 4096) != sqOf i &&
      sqOf (i / 64) != sqOf i &&
      krkWhiteOK T (krkDepth (T i)) (sqOf (i / 4096)) (sqOf (i / 64)) (sqOf i)
        (sqOf (krkSrc (T i))) (sqOf (krkDst (T i))))

/-! ### Soundness -/

/-- The position after an accepted White move and the forced mate from it. -/
theorem krk_afterWhiteOK_sound (T : Nat → Nat) (d : Nat) (wk' wq' bk : Square)
    (hbk₁ : bk ≠ wk') (hbk₂ : bk ≠ wq')
    (ih : ∀ e < d + 1, ∀ wk wq bk : Square, krkDepth (T (kqkIdx wk.val wq.val bk.val)) = e →
      e ≠ 0 → ∀ h, ForcesMate .white e (krkPos wk wq bk .white h))
    (hok : krkAfterWhiteOK T (d + 1) wk' wq' bk = true) (h : Nat) :
    ForcesMate .white d (krkPos wk' wq' bk .black h) := by
  simp only [krkAfterWhiteOK, Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨_, hok⟩ := hok
  have hlm : legalMoves (krkPos wk' wq' bk .black h) = legalMoves (krkPos wk' wq' bk .black 0) :=
    rfl
  split at hok
  · rename_i hnil
    refine .mated d _ rfl ?_
    simp only [isCheckmate, hlm, hnil, List.isEmpty_nil, Bool.and_true]
    exact hok
  · rename_i m₀ ms hcons
    have hne : legalMoves (krkPos wk' wq' bk .black h) ≠ [] := by rw [hlm, hcons]; simp
    have hall : ∀ m ∈ legalMoves (krkPos wk' wq' bk .black h),
        krkReplyOK T (d + 1) wk' wq' bk m = true :=
      fun m hm => List.all_eq_true.1 hok m (by rw [← hcons, ← hlm]; exact hm)
    refine .defend d _ rfl hne fun m hm => ?_
    have hr := hall m hm
    simp only [krkReplyOK, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at hr
    obtain ⟨⟨⟨⟨⟨⟨⟨hsrc, hpro⟩, hd₀⟩, hd₁⟩, hd₂⟩, hd₃⟩, hd₄⟩, hpos, hlt⟩ := hr
    have hm' : m = ⟨bk, m.dst, none⟩ := by cases m; simp_all
    rw [hm', play_krk_black wk' wq' bk m.dst h hbk₁ hbk₂ hd₀ hd₁ hd₂ hd₃ hd₄]
    have := ih _ (by omega) wk' wq' m.dst rfl (by omega) (h + 1)
    have := this.mono (d - krkDepth (T (kqkIdx wk'.val wq'.val m.dst.val)))
    rwa [show krkDepth (T (kqkIdx wk'.val wq'.val m.dst.val)) +
      (d - krkDepth (T (kqkIdx wk'.val wq'.val m.dst.val))) = d by omega] at this

/-- **Soundness of the KRK table check**: if every entry passes `krkStateOK`, then every entry of
nonzero depth `d` is a forced mate for White within `d` moves, for any halfmove clock. -/
theorem krk_table_sound (T : Nat → Nat) (hT : ∀ i, i < 262144 → krkStateOK T i = true) :
    ∀ d, ∀ wk wq bk : Square, krkDepth (T (kqkIdx wk.val wq.val bk.val)) = d → d ≠ 0 →
      ∀ h, ForcesMate .white d (krkPos wk wq bk .white h) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro wk wq bk hd hd0 h
  have hi : kqkIdx wk.val wq.val bk.val < 262144 := by
    have := wk.isLt; have := wq.isLt; have := bk.isLt; simp only [kqkIdx]; omega
  have hs := hT _ hi
  obtain ⟨e₁, e₂, e₃⟩ := sqOf_kqkIdx wk wq bk
  simp only [krkStateOK, e₁, e₂, e₃, hd, Bool.or_eq_true, beq_iff_eq, hd0, false_or,
    Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hs
  obtain ⟨⟨⟨⟨_, h₁⟩, h₂⟩, h₃⟩, hw⟩ := hs
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have ih' : ∀ e < d' + 1, ∀ wk wq bk : Square, krkDepth (T (kqkIdx wk.val wq.val bk.val)) = e →
      e ≠ 0 → ∀ h, ForcesMate .white e (krkPos wk wq bk .white h) :=
    fun e he => ih e he
  generalize sqOf (krkSrc (T (kqkIdx wk.val wq.val bk.val))) = src at hw
  generalize sqOf (krkDst (T (kqkIdx wk.val wq.val bk.val))) = dst at hw
  simp only [krkWhiteOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    List.contains_iff_mem] at hw
  rcases hw with ⟨⟨⟨⟨⟨⟨⟨_, hd₀⟩, hd₁⟩, hd₂⟩, hd₃⟩, hd₄⟩, hmem⟩, hok⟩ |
      ⟨⟨⟨⟨⟨_, hd₀⟩, hd₁⟩, hd₂⟩, hmem⟩, hok⟩
  · have hplay := play_krk_king wk wq bk dst h h₁ h₂ hd₀ hd₁ hd₂ hd₃ hd₄
    have hc : inCheck (krkBoard dst wq bk) .white = false := by
      have := hok
      simp only [krkAfterWhiteOK, Bool.and_eq_true, Bool.not_eq_true'] at this
      exact this.1
    have hlegal : (⟨wk, dst, none⟩ : Move) ∈ legalMoves (krkPos wk wq bk .white h) :=
      mem_legalMoves_of _ wk .king _ (by simp [krkPos, krkBoard]) hmem
        (by rw [hplay]; exact hc)
    refine .attack d' _ _ rfl hlegal ?_
    rw [hplay]
    exact krk_afterWhiteOK_sound T d' dst wq bk (Ne.symm hd₂) (Ne.symm h₃) ih' hok (h + 1)
  · have hplay := play_krk_rook wk wq bk dst h h₁ h₃ hd₀ hd₁ hd₂
    have hc : inCheck (krkBoard wk dst bk) .white = false := by
      have := hok
      simp only [krkAfterWhiteOK, Bool.and_eq_true, Bool.not_eq_true'] at this
      exact this.1
    have hlegal : (⟨wq, dst, none⟩ : Move) ∈ legalMoves (krkPos wk wq bk .white h) :=
      mem_legalMoves_of _ wq .rook _ (by simp [krkPos, krkBoard, Ne.symm h₁]) hmem
        (by rw [hplay]; exact hc)
    refine .attack d' _ _ rfl hlegal ?_
    rw [hplay]
    exact krk_afterWhiteOK_sound T d' wk dst bk (Ne.symm h₂) (Ne.symm hd₂) ih' hok (h + 1)

end LeanTheory.Chess
