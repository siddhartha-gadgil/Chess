/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.Chess.Game
public import LeanTheory.Certificates.KernelFact

/-!
# Dead positions: bare kings and king and knight against king

Note `N-07`. FIDE Article 5.2.2 calls a position *dead* when no sequence of legal moves leads to
a checkmate; the kernel encodes this semantically as `IsDead` (`Kernel/Chess/Game`), quantifying
over all move sequences. This file proves dead positions by **invariants closed under legal
moves that exclude checkmate**, reasoning symbolically about `pseudoMoves`, `play` and
`inCheck` (no enumeration, no `decide`).

* `dead_KK`: every well-formed position whose only pieces are kings is dead. Invariant `KKInv`:
  the board is exactly two non-adjacent kings (`kk w k`).
* `dead_KNK`: every well-formed position with the two kings and exactly one knight (of either
  colour) is dead. Invariant `DInv := KKInv ∨ KNInv`; the knight side can never be in check
  (only a lone king could give it), and the lone king, when checked by the knight, always has a
  flight square (`knk_flight`: an orthogonal neighbour has the colour of the knight's square, so
  the knight does not attack it, and the enemy king cannot cover two perpendicular orthogonal
  neighbours without standing next to the lone king). Capturing the knight leads to `KKInv`.
* Fixtures: concrete dead `KK` and `KNK` positions (`kernel_fact` for the side conditions),
  rejected fixtures, and `not_dead_KQK_example`, a `KQK` position with a mate in one, which
  guards against an over-broad `IsDead`.

Scope: castling flags, the en passant field and the halfmove clock are arbitrary (castling needs
a rook; pawn moves need a pawn). `KBK` (king and bishop against king) is not yet proved; it needs
the same colour argument for sliding attacks (see the report of note `N-07`).
-/

@[expose] public section

namespace LeanTheory.Chess

/-- `Square.shift` in coordinates: the shifted square exists iff the new file and rank are on
the board, and its index is `8 * rank + file`. -/
theorem shift_eq_some {s t : Square} {df dr : Int} :
    s.shift df dr = some t ↔
      0 ≤ (s.file : Int) + df ∧ (s.file : Int) + df < 8 ∧ 0 ≤ (s.rank : Int) + dr ∧
        (s.rank : Int) + dr < 8 ∧ (t.val : Int) = ((s.rank : Int) + dr) * 8 + (s.file + df) := by
  unfold Square.shift Square.ofNat?
  simp only []
  split_ifs with h1 h2
  · simp only [Option.some.injEq, Fin.ext_iff, Square.file, Square.rank] at *; omega
  · simp only [false_iff, Square.file, Square.rank] at *; omega
  · simp only [false_iff]; omega

/-- `kingAdj s t`: the squares are a king step apart (`t` is `s` displaced by one of
`kingDeltas`). -/
def kingAdj (s t : Square) : Bool := kingDeltas.any fun d => s.shift d.1 d.2 == some t

/-- `kingAdj` in coordinates: distinct squares whose files and ranks differ by at most one. -/
theorem kingAdj_iff {s t : Square} : kingAdj s t = true ↔
    s ≠ t ∧ ((s.val % 8 : Nat) : Int) - (t.val % 8 : Nat) ≤ 1 ∧
      ((t.val % 8 : Nat) : Int) - (s.val % 8 : Nat) ≤ 1 ∧
      ((s.val / 8 : Nat) : Int) - (t.val / 8 : Nat) ≤ 1 ∧
      ((t.val / 8 : Nat) : Int) - (s.val / 8 : Nat) ≤ 1 := by
  simp only [kingAdj, kingDeltas, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
    beq_iff_eq, shift_eq_some, Square.file, Square.rank, ne_eq, Fin.ext_iff]
  omega

/-- King adjacency is symmetric. -/
theorem kingAdj_comm (s t : Square) : kingAdj s t = kingAdj t s := by
  rw [Bool.eq_iff_iff, kingAdj_iff, kingAdj_iff, ne_eq, ne_eq, Fin.ext_iff, Fin.ext_iff]
  omega

/-- Every piece on the board is a king (either colour). -/
def onlyKings (b : Board) : Bool :=
  allSquares.all fun s => match b s with
    | some pc => pc.kind == .king
    | none => true

/-- Specification of `onlyKings`: every piece on the board is a king. -/
theorem onlyKings_spec {b : Board} (h : onlyKings b = true) {s : Square} {pc : Piece}
    (hs : b s = some pc) : pc.kind = .king := by
  simp only [onlyKings, List.all_eq_true] at h
  have := h s (mem_allSquares s)
  simp only [hs, beq_iff_eq] at this
  exact this

/-- The piece found by `firstOnRay` stands on some square of the board. -/
theorem firstOnRay_some {b : Board} {df dr : Int} :
    ∀ {n : Nat} {s : Square} {pc : Piece}, firstOnRay b df dr n s = some pc →
      ∃ t, b t = some pc := by
  intro n
  induction n with
  | zero => intro s pc h; simp [firstOnRay] at h
  | succ n ih =>
    intro s pc h
    simp only [firstOnRay] at h
    split at h
    · simp at h
    · split at h
      · rename_i t _ _ p hp
        refine ⟨t, ?_⟩
        simp_all
      · exact ih h

/-- `pieceAtOffsets` is `false` for a piece that is nowhere on the board. -/
theorem pieceAtOffsets_eq_false {b : Board} {pc : Piece} (h : ∀ t, b t ≠ some pc)
    (s : Square) (ds : List (Int × Int)) : pieceAtOffsets b pc s ds = false := by
  simp only [pieceAtOffsets, List.any_eq_false]
  intro d _
  split <;> simp_all

/-- `pieceAtOffsets` for a piece standing exactly on `t`: some offset leads from `s` to `t`. -/
theorem pieceAtOffsets_unique {b : Board} {pc : Piece} {t : Square}
    (h : ∀ u, b u = some pc ↔ u = t) (s : Square) (ds : List (Int × Int)) :
    pieceAtOffsets b pc s ds = ds.any fun d => s.shift d.1 d.2 == some t := by
  unfold pieceAtOffsets
  congr 1
  funext d
  split <;> simp_all

/-- On a board with kings only, a square is attacked exactly when an enemy king is a king
step away. -/
theorem attackedBy_onlyKings {b : Board} (hb : onlyKings b = true) (c : Color) (s : Square) :
    attackedBy b c s = pieceAtOffsets b ⟨c, .king⟩ s kingDeltas := by
  have hk : ∀ k, k ≠ PieceType.king → ∀ t, b t ≠ some ⟨c, k⟩ :=
    fun k hk t ht => hk (onlyKings_spec hb ht)
  have hray : ∀ df dr pc, firstOnRay b df dr 7 s = some pc → pc.kind = .king := by
    intro df dr pc h
    obtain ⟨t, ht⟩ := firstOnRay_some h
    exact onlyKings_spec hb ht
  unfold attackedBy
  rw [pieceAtOffsets_eq_false (hk .knight (by simp)), pieceAtOffsets_eq_false (hk .pawn (by simp))]
  rw [Bool.eq_iff_iff]
  simp only [Bool.false_or, Bool.or_false, Bool.or_eq_true, List.any_eq_true]
  refine ⟨fun h => ?_, fun h => Or.inl (Or.inl h)⟩
  rcases h with (h | ⟨d, _, hd⟩) | ⟨d, _, hd⟩
  · exact h
  all_goals
    split at hd
    · rename_i p hp
      have := hray _ _ _ hp
      obtain ⟨pc, pk⟩ := p
      simp only at this
      subst this
      simp at hd
    · simp at hd

/-- The board with the white king on `w`, the black king on `k` and nothing else. -/
def kk (w k : Square) : Board := fun s =>
  if s = w then some ⟨.white, .king⟩ else if s = k then some ⟨.black, .king⟩ else none

/-- The white king of `kk w k` stands exactly on `w`. -/
theorem kk_eq_wk {w k s : Square} : kk w k s = some ⟨.white, .king⟩ ↔ s = w := by
  unfold kk; split_ifs <;> simp_all

/-- The black king of `kk w k` stands exactly on `k` (for `w ≠ k`). -/
theorem kk_eq_bk {w k s : Square} (hwk : w ≠ k) : kk w k s = some ⟨.black, .king⟩ ↔ s = k := by
  unfold kk; split_ifs <;> simp_all

/-- `kk w k` has kings only. -/
theorem onlyKings_kk (w k : Square) : onlyKings (kk w k) = true := by
  simp only [onlyKings, List.all_eq_true]
  intro s _
  unfold kk; split_ifs <;> simp

/-- `find?` returns the unique element satisfying the predicate. -/
theorem find?_unique {α : Type} {l : List α} {p : α → Bool} {x : α} (hx : x ∈ l)
    (hp : ∀ y, p y = true ↔ y = x) : l.find? p = some x := by
  cases h : l.find? p with
  | none =>
    rw [List.find?_eq_none] at h
    exact absurd ((hp x).2 rfl) (h x hx)
  | some y => rw [(hp y).1 (List.find?_some h)]

/-- `kingSquare` finds a king standing on a unique square. -/
theorem kingSquare_unique {b : Board} {c : Color} {t : Square}
    (h : ∀ u, b u = some ⟨c, .king⟩ ↔ u = t) : kingSquare b c = some t :=
  find?_unique (mem_allSquares t) (fun y => by simp [h])

/-- On `kk w k`, White is in check iff the kings are adjacent. -/
theorem inCheck_kk_white {w k : Square} (hwk : w ≠ k) : inCheck (kk w k) .white = kingAdj w k := by
  unfold inCheck
  rw [kingSquare_unique (fun _ => kk_eq_wk)]
  simp only [Color.other]
  rw [attackedBy_onlyKings (onlyKings_kk w k), pieceAtOffsets_unique (fun _ => kk_eq_bk hwk)]
  rfl

/-- On `kk w k`, Black is in check iff the kings are adjacent. -/
theorem inCheck_kk_black {w k : Square} (hwk : w ≠ k) : inCheck (kk w k) .black = kingAdj k w := by
  unfold inCheck
  rw [kingSquare_unique (fun _ => kk_eq_bk hwk)]
  simp only [Color.other]
  rw [attackedBy_onlyKings (onlyKings_kk w k), pieceAtOffsets_unique (fun _ => kk_eq_wk)]
  rfl

/-- On a kings-only board every pseudo-legal move is a plain king step of the side to move
(no promotion; castling is impossible without rooks). -/
theorem mem_pseudoMoves_onlyKings {p : Position} (hb : onlyKings p.board = true) {m : Move}
    (hm : m ∈ pseudoMoves p) :
    p.board m.src = some ⟨p.turn, .king⟩ ∧ m.promo = none ∧ kingAdj m.src m.dst = true := by
  have hr : castlingMoves p = [] := by
    have : ∀ s c, (p.board s == some ⟨c, .rook⟩) = false := by
      intro s c
      cases h : p.board s with
      | none => rfl
      | some pc =>
        have := onlyKings_spec hb h
        obtain ⟨pc, pk⟩ := pc
        simp only at this
        subst this
        simp
    simp [castlingMoves, this]
  simp only [pseudoMoves, hr, List.append_nil, List.mem_flatMap] at hm
  obtain ⟨s, -, hm⟩ := hm
  split at hm
  · rename_i pc hs
    split_ifs at hm with hc
    · have hk := onlyKings_spec hb hs
      obtain ⟨c, k⟩ := pc
      simp only at hk hc
      subst hk hc
      simp only [pieceMoves, List.mem_map] at hm
      obtain ⟨t, ht, rfl⟩ := hm
      simp only [stepTargets, List.mem_filterMap] at ht
      obtain ⟨d, hd, ht⟩ := ht
      refine ⟨hs, rfl, ?_⟩
      simp only [kingAdj, List.any_eq_true, beq_iff_eq]
      refine ⟨d, hd, ?_⟩
      split at ht
      · rename_i u hu
        split at ht
        · split_ifs at ht
          simp_all
        · simp_all
      · simp at ht
    · simp at hm
  · simp at hm

/-- The board after a plain king step: the king moves from `src` to `dst` (no rook moves,
since a king step is never a two-square move). -/
theorem play_board_kingMove {p : Position} {m : Move} (hs : p.board m.src = some ⟨p.turn, .king⟩)
    (hp : m.promo = none) (ha : kingAdj m.src m.dst = true) :
    (play p m).board =
      fun t => if t = m.dst then p.board m.src else if t = m.src then none else p.board t := by
  have h2 : ¬ (m.dst.val = m.src.val + 2) := by have := kingAdj_iff.1 ha; omega
  have h2' : ¬ (m.src.val = m.dst.val + 2) := by have := kingAdj_iff.1 ha; omega
  simp [play, hs, hp, h2, h2']

/-- **The bare-kings invariant**: the board is `kk w k` with non-adjacent kings. Turn,
castling flags, en passant target and halfmove clock are arbitrary. -/
def KKInv (p : Position) : Prop := ∃ w k, w ≠ k ∧ p.board = kk w k ∧ kingAdj w k = false

/-- Under the bare-kings invariant the side to move is not in check. -/
theorem KKInv.inCheck_eq_false {p : Position} (h : KKInv p) : inCheck p.board p.turn = false := by
  obtain ⟨w, k, hwk, hb, ha⟩ := h
  rw [hb]
  cases p.turn
  · rw [inCheck_kk_white hwk, ha]
  · rw [inCheck_kk_black hwk, kingAdj_comm, ha]

/-- Under the bare-kings invariant there is no checkmate. -/
theorem KKInv.not_checkmate {p : Position} (h : KKInv p) : isCheckmate p = false := by
  simp [isCheckmate, h.inCheck_eq_false]

/-- The bare-kings invariant is preserved by every legal move. -/
theorem KKInv.play {p : Position} {m : Move} (h : KKInv p) (hm : m ∈ legalMoves p) :
    KKInv (play p m) := by
  obtain ⟨w, k, hwk, hb, ha⟩ := h
  simp only [legalMoves, List.mem_filter, Bool.not_eq_true'] at hm
  obtain ⟨hps, hchk⟩ := hm
  have hok : onlyKings p.board = true := hb ▸ onlyKings_kk w k
  obtain ⟨hs, hpr, had⟩ := mem_pseudoMoves_onlyKings hok hps
  have hpb := play_board_kingMove hs hpr had
  have hne := (kingAdj_iff.1 had).1
  rw [hpb] at hchk
  rw [hb] at hs
  cases hturn : p.turn <;> rw [hturn] at hs hchk
  · have hsw : m.src = w := kk_eq_wk.1 hs
    subst hsw
    have hdk : m.dst ≠ k := by rintro rfl; rw [ha] at had; exact Bool.false_ne_true had
    have hbd : (fun t => if t = m.dst then p.board m.src else if t = m.src then none else
        p.board t) = kk m.dst k := by
      funext x; simp only [hb, kk]; split_ifs <;> simp_all
    refine ⟨m.dst, k, hdk, hpb.trans hbd, ?_⟩
    rw [hbd, inCheck_kk_white hdk] at hchk
    exact hchk
  · have hsk : m.src = k := (kk_eq_bk hwk).1 hs
    subst hsk
    have hdw : m.dst ≠ w := by
      rintro rfl; rw [kingAdj_comm, ha] at had; exact Bool.false_ne_true had
    have hbd : (fun t => if t = m.dst then p.board m.src else if t = m.src then none else
        p.board t) = kk w m.dst := by
      funext x; simp only [hb, kk]; split_ifs <;> simp_all
    refine ⟨w, m.dst, Ne.symm hdw, hpb.trans hbd, ?_⟩
    rw [hbd, inCheck_kk_black (Ne.symm hdw), kingAdj_comm] at hchk
    exact hchk

/-- A position satisfying the bare-kings invariant is dead. -/
theorem KKInv.isDead {p : Position} (h : KKInv p) : IsDead p := by
  intro ms
  induction ms generalizing p with
  | nil =>
    intro q hq
    simp only [playLegal, Option.some.injEq] at hq
    subst hq
    exact h.not_checkmate
  | cons m ms ih =>
    intro q hq
    simp only [playLegal] at hq
    split_ifs at hq with hl
    exact ih (h.play ((isLegal_iff _ _).1 hl)) q hq

/-- A piece occurring exactly once stands on a unique square. -/
theorem countPiece_eq_one {b : Board} {pc : Piece} (h : countPiece b pc = 1) :
    ∃ s, ∀ u, b u = some pc ↔ u = s := by
  unfold countPiece at h
  obtain ⟨s, hs⟩ := List.length_eq_one_iff.1 h
  refine ⟨s, fun u => ⟨fun hu => ?_, fun hu => ?_⟩⟩
  · have : u ∈ allSquares.filter fun s => b s == some pc :=
      List.mem_filter.2 ⟨mem_allSquares u, by simp [hu]⟩
    rw [hs] at this
    simpa using this
  · subst hu
    have : u ∈ [u] := by simp
    rw [← hs] at this
    simpa using (List.mem_filter.1 this).2

/-- A well-formed kings-only position satisfies the bare-kings invariant. -/
theorem KKInv.of_wellFormed {p : Position} (hw : wellFormed p = true)
    (hk : onlyKings p.board = true) : KKInv p := by
  simp only [wellFormed, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hw
  obtain ⟨⟨⟨⟨hW, hB⟩, -⟩, hc⟩, -⟩ := hw
  obtain ⟨w, hw⟩ := countPiece_eq_one hW
  obtain ⟨k, hk'⟩ := countPiece_eq_one hB
  have hwk : w ≠ k := by
    rintro rfl
    have h1 := (hw w).2 rfl
    rw [(hk' w).2 rfl] at h1
    simp at h1
  have hb : p.board = kk w k := by
    funext s
    unfold kk
    split_ifs with h1 h2
    · exact (hw s).2 h1
    · exact (hk' s).2 h2
    · cases hs : p.board s with
      | none => rfl
      | some pc =>
        have := onlyKings_spec hk hs
        obtain ⟨c, pk⟩ := pc
        simp only at this
        subst this
        cases c
        · exact absurd ((hw s).1 hs) h1
        · exact absurd ((hk' s).1 hs) h2
  refine ⟨w, k, hwk, hb, ?_⟩
  rw [hb] at hc
  cases hturn : p.turn <;> rw [hturn] at hc <;> simp only [Color.other] at hc
  · rwa [inCheck_kk_black hwk, kingAdj_comm] at hc
  · rwa [inCheck_kk_white hwk] at hc

/-- **King against king is dead** (FIDE 5.2.2, note `N-07`): every well-formed position whose
only pieces are kings is dead. Castling flags, the en passant field and the halfmove clock
are arbitrary. -/
theorem dead_KK (p : Position) (hw : wellFormed p = true) (hk : onlyKings p.board = true) :
    IsDead p :=
  (KKInv.of_wellFormed hw hk).isDead

/-! ### King and knight against king -/

/-- Every colour is `c` or `c.other`. -/
theorem Color.eq_or_eq_other (t c : Color) : t = c ∨ t = c.other := by
  cases t <;> cases c <;> simp [Color.other]

/-- `knightAdj s t`: `t` is a knight's move away from `s`. -/
def knightAdj (s t : Square) : Bool := knightDeltas.any fun d => s.shift d.1 d.2 == some t

/-- A knight's move changes file and rank by `(±1, ±2)` or `(±2, ±1)`. -/
theorem knightAdj_imp {s t : Square} (h : knightAdj s t = true) :
    ((((t.val % 8 : Nat) : Int) - (s.val % 8 : Nat) = 1 ∨
        ((t.val % 8 : Nat) : Int) - (s.val % 8 : Nat) = -1) ∧
      (((t.val / 8 : Nat) : Int) - (s.val / 8 : Nat) = 2 ∨
        ((t.val / 8 : Nat) : Int) - (s.val / 8 : Nat) = -2)) ∨
    ((((t.val % 8 : Nat) : Int) - (s.val % 8 : Nat) = 2 ∨
        ((t.val % 8 : Nat) : Int) - (s.val % 8 : Nat) = -2) ∧
      (((t.val / 8 : Nat) : Int) - (s.val / 8 : Nat) = 1 ∨
        ((t.val / 8 : Nat) : Int) - (s.val / 8 : Nat) = -1)) := by
  simp only [knightAdj, knightDeltas, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
    beq_iff_eq, shift_eq_some, Square.file, Square.rank] at h
  rcases h with h | h | h | h | h | h | h | h <;> omega

/-- Shifting back by the opposite displacement returns to the start. -/
theorem shift_neg {s t : Square} {df dr : Int} (h : s.shift df dr = some t) :
    t.shift (-df) (-dr) = some s := by
  rw [shift_eq_some] at h ⊢
  simp only [Square.file, Square.rank] at h ⊢
  omega

/-- Knight adjacency is symmetric. -/
theorem knightAdj_comm (s t : Square) : knightAdj s t = knightAdj t s := by
  have key : ∀ s t : Square, knightAdj s t = true → knightAdj t s = true := by
    intro s t h
    simp only [knightAdj, List.any_eq_true, beq_iff_eq] at h ⊢
    obtain ⟨d, hd, h⟩ := h
    refine ⟨(-d.1, -d.2), ?_, shift_neg h⟩
    simp only [knightDeltas, List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  rw [Bool.eq_iff_iff]
  exact ⟨key s t, key t s⟩

/-- On a board with kings and knights only, a square is attacked exactly when an enemy king
is a king step away or an enemy knight a knight's move away. -/
theorem attackedBy_KN {b : Board}
    (hb : ∀ s pc, b s = some pc → pc.kind = .king ∨ pc.kind = .knight) (c : Color) (s : Square) :
    attackedBy b c s =
      (pieceAtOffsets b ⟨c, .king⟩ s kingDeltas ||
        pieceAtOffsets b ⟨c, .knight⟩ s knightDeltas) := by
  have hray : ∀ df dr pc, firstOnRay b df dr 7 s = some pc →
      pc.kind = .king ∨ pc.kind = .knight := by
    intro df dr pc h
    obtain ⟨t, ht⟩ := firstOnRay_some h
    exact hb _ _ ht
  unfold attackedBy
  rw [pieceAtOffsets_eq_false (pc := ⟨c, .pawn⟩) (fun t ht => by simpa using hb _ _ ht)]
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_false, Bool.or_eq_true, List.any_eq_true]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ((h | h) | ⟨d, _, hd⟩) | ⟨d, _, hd⟩
    · exact Or.inr h
    · exact Or.inl h
    all_goals
      split at hd
      · rename_i p hp
        obtain ⟨pc, pk⟩ := p
        rcases hray _ _ _ hp with h | h <;> simp only at h <;> subst h <;> simp at hd
      · simp at hd
  · rcases h with h | h
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inl (Or.inl h))

/-- The board with the king of `c` on `a`, the king of `c.other` on `e`, the knight of `c` on
`n` and nothing else. -/
def knb (c : Color) (a e n : Square) : Board := fun s =>
  if s = a then some ⟨c, .king⟩ else if s = e then some ⟨c.other, .king⟩
  else if s = n then some ⟨c, .knight⟩ else none

/-- `knb` has only kings and knights. -/
theorem knb_kind {c : Color} {a e n s : Square} {pc : Piece} (h : knb c a e n s = some pc) :
    pc.kind = .king ∨ pc.kind = .knight := by
  unfold knb at h; split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;> simp

/-- The king of `c` stands exactly on `a`. -/
theorem knb_ck {c : Color} {a e n s : Square} : knb c a e n s = some ⟨c, .king⟩ ↔ s = a := by
  have := Color.other_ne c
  unfold knb; split_ifs <;> simp_all

/-- The king of `c.other` stands exactly on `e`. -/
theorem knb_ok {c : Color} {a e n s : Square} (hae : a ≠ e) :
    knb c a e n s = some ⟨c.other, .king⟩ ↔ s = e := by
  have := Color.other_ne c
  unfold knb; split_ifs <;> simp_all [eq_comm]

/-- The knight of `c` stands exactly on `n`. -/
theorem knb_cn {c : Color} {a e n s : Square} (hna : n ≠ a) (hne : n ≠ e) :
    knb c a e n s = some ⟨c, .knight⟩ ↔ s = n := by
  have := Ne.symm hna
  have := Ne.symm hne
  unfold knb; split_ifs <;> simp_all

/-- The lone side has no knight. -/
theorem knb_on {c : Color} {a e n : Square} (s : Square) :
    knb c a e n s ≠ some ⟨c.other, .knight⟩ := by
  have := Color.other_ne c
  unfold knb; split_ifs <;> simp_all [eq_comm]

/-- The side with the knight is in check iff the kings are adjacent. -/
theorem inCheck_knb_strong {c : Color} {a e n : Square} (hae : a ≠ e) :
    inCheck (knb c a e n) c = kingAdj a e := by
  unfold inCheck
  rw [kingSquare_unique (fun _ => knb_ck)]
  simp only
  rw [attackedBy_KN (fun _ _ => knb_kind), pieceAtOffsets_unique (fun _ => knb_ok hae),
    pieceAtOffsets_eq_false knb_on, Bool.or_false]
  rfl

/-- The lone king is in check iff it is adjacent to the enemy king or attacked by the knight. -/
theorem inCheck_knb_lone {c : Color} {a e n : Square} (hae : a ≠ e) (hna : n ≠ a) (hne : n ≠ e) :
    inCheck (knb c a e n) c.other = (kingAdj e a || knightAdj e n) := by
  unfold inCheck
  rw [kingSquare_unique (fun _ => knb_ok hae)]
  simp only [Color.other_other]
  rw [attackedBy_KN (fun _ _ => knb_kind), pieceAtOffsets_unique (fun _ => knb_ck),
    pieceAtOffsets_unique (fun _ => knb_cn hna hne)]
  rfl

/-- Membership in `stepTargets`: a displaced square not holding a piece of the mover. -/
theorem mem_stepTargets {b : Board} {c : Color} {s t : Square} {ds : List (Int × Int)} :
    t ∈ stepTargets b c s ds ↔
      (∃ d ∈ ds, s.shift d.1 d.2 = some t) ∧ ∀ pc, b t = some pc → pc.color ≠ c := by
  simp only [stepTargets, List.mem_filterMap]
  constructor
  · rintro ⟨d, hd, ht⟩
    split at ht
    · rename_i u hu
      split at ht
      · rename_i q hq
        split_ifs at ht with hc
        simp only [Option.some.injEq] at ht
        subst ht
        exact ⟨⟨d, hd, hu⟩, fun pc h => by simp_all⟩
      · simp only [Option.some.injEq] at ht
        subst ht
        exact ⟨⟨d, hd, hu⟩, fun pc h => by simp_all⟩
    · simp at ht
  · rintro ⟨⟨d, hd, hu⟩, hc⟩
    refine ⟨d, hd, ?_⟩
    rw [hu]
    simp only
    cases hq : b t with
    | none => rfl
    | some q => simp [hc q hq]

/-- On a board with kings and knights only, a pseudo-legal move is a plain king step or knight
move of the side to move, onto a square without a piece of its own. -/
theorem mem_pseudoMoves_KN {p : Position}
    (hb : ∀ s pc, p.board s = some pc → pc.kind = .king ∨ pc.kind = .knight) {m : Move}
    (hm : m ∈ pseudoMoves p) :
    m.promo = none ∧
      ((p.board m.src = some ⟨p.turn, .king⟩ ∧ kingAdj m.src m.dst = true) ∨
        (p.board m.src = some ⟨p.turn, .knight⟩ ∧ knightAdj m.src m.dst = true)) ∧
      ∀ pc, p.board m.dst = some pc → pc.color ≠ p.turn := by
  have hr : castlingMoves p = [] := by
    have : ∀ s c, (p.board s == some ⟨c, .rook⟩) = false := by
      intro s c
      cases h : p.board s with
      | none => rfl
      | some pc =>
        obtain ⟨pc, pk⟩ := pc
        rcases hb _ _ h with h' | h' <;> simp only at h' <;> subst h' <;> simp
    simp [castlingMoves, this]
  simp only [pseudoMoves, hr, List.append_nil, List.mem_flatMap] at hm
  obtain ⟨s, -, hm⟩ := hm
  split at hm
  · rename_i pc hs
    split_ifs at hm with hc
    · obtain ⟨c, k⟩ := pc
      simp only at hc
      subst hc
      rcases hb _ _ hs with hk | hk <;> simp only at hk <;> subst hk <;>
        simp only [pieceMoves, List.mem_map] at hm <;>
        obtain ⟨t, ht, rfl⟩ := hm <;>
        obtain ⟨⟨d, hd, hu⟩, hc⟩ := mem_stepTargets.1 ht
      · refine ⟨rfl, Or.inl ⟨hs, ?_⟩, hc⟩
        simp only [kingAdj, List.any_eq_true, beq_iff_eq]
        exact ⟨d, hd, hu⟩
      · refine ⟨rfl, Or.inr ⟨hs, ?_⟩, hc⟩
        simp only [knightAdj, List.any_eq_true, beq_iff_eq]
        exact ⟨d, hd, hu⟩
    · simp at hm
  · simp at hm

/-- The board after a plain move of a non-pawn piece (a king moving one step): the piece
moves from `src` to `dst`, capturing whatever stands there. -/
theorem play_board_simple {p : Position} {m : Move} {kd : PieceType}
    (hs : p.board m.src = some ⟨p.turn, kd⟩) (hkd : kd ≠ .pawn) (hp : m.promo = none)
    (ha : kd = .king → kingAdj m.src m.dst = true) :
    (play p m).board =
      fun t => if t = m.dst then p.board m.src else if t = m.src then none else p.board t := by
  by_cases hk : kd = .king
  · subst hk
    exact play_board_kingMove hs hp (ha rfl)
  · simp [play, hs, hp, hk, hkd]

/-- A king step onto a square without a piece of the mover is pseudo-legal. -/
theorem kingMove_mem_pseudoMoves {p : Position} {e t : Square}
    (he : p.board e = some ⟨p.turn, .king⟩) (ha : kingAdj e t = true)
    (ht : ∀ pc, p.board t = some pc → pc.color ≠ p.turn) : ⟨e, t, none⟩ ∈ pseudoMoves p := by
  unfold pseudoMoves
  refine List.mem_append_left _ (List.mem_flatMap.2 ⟨e, mem_allSquares e, ?_⟩)
  simp only [he, ite_true]
  simp only [pieceMoves, List.mem_map]
  refine ⟨t, mem_stepTargets.2 ⟨?_, ht⟩, rfl⟩
  simpa [kingAdj] using ha

/-- A knight's move changes the colour of the square. -/
theorem knightAdj_parity {s t : Square} (h : knightAdj s t = true) :
    (s.val % 8 + s.val / 8) % 2 ≠ (t.val % 8 + t.val / 8) % 2 := by
  have := knightAdj_imp h
  omega

/-- Geometric core with explicit candidates: given a horizontal neighbour `t₁` and a vertical
neighbour `t₂` of the lone king `e`, one of them is a flight square. -/
theorem knk_flight_of {a e n t₁ t₂ : Square} (hae : kingAdj a e = false) (ha : a ≠ e)
    (hn : knightAdj e n = true)
    (h₁ : t₁.val / 8 = e.val / 8 ∧ (t₁.val % 8 = e.val % 8 + 1 ∨ t₁.val % 8 + 1 = e.val % 8))
    (h₂ : t₂.val % 8 = e.val % 8 ∧ (t₂.val / 8 = e.val / 8 + 1 ∨ t₂.val / 8 + 1 = e.val / 8)) :
    ∃ t, kingAdj e t = true ∧ kingAdj t a = false ∧ t ≠ a ∧ knightAdj t n = false := by
  have hn' := knightAdj_parity hn
  have hae' : ¬ (kingAdj a e = true) := by simp [hae]
  rw [kingAdj_iff] at hae'
  simp only [ne_eq, Fin.ext_iff] at hae' ha
  have nk : ∀ t : Square, ((t.val % 8 + t.val / 8) % 2 ≠ (e.val % 8 + e.val / 8) % 2) →
      knightAdj t n = false := by
    intro t ht
    cases h : knightAdj t n
    · rfl
    · have := knightAdj_parity h
      omega
  have adj : ∀ t : Square, (t.val / 8 = e.val / 8 ∧
      (t.val % 8 = e.val % 8 + 1 ∨ t.val % 8 + 1 = e.val % 8)) ∨
      (t.val % 8 = e.val % 8 ∧ (t.val / 8 = e.val / 8 + 1 ∨ t.val / 8 + 1 = e.val / 8)) →
      kingAdj e t = true := by
    intro t ht
    rw [kingAdj_iff]
    simp only [ne_eq, Fin.ext_iff]
    omega
  by_cases hc : kingAdj t₁ a = false ∧ t₁ ≠ a
  · exact ⟨t₁, adj _ (Or.inl h₁), hc.1, hc.2, nk _ (by omega)⟩
  · refine ⟨t₂, adj _ (Or.inr h₂), ?_, ?_, nk _ (by omega)⟩
    · rw [Bool.eq_false_iff, ne_eq, kingAdj_iff]
      rw [Bool.eq_false_iff, ne_eq, kingAdj_iff] at hc
      simp only [ne_eq, Fin.ext_iff] at hc ⊢
      omega
    · rw [Bool.eq_false_iff, ne_eq, kingAdj_iff] at hc
      simp only [ne_eq, Fin.ext_iff] at hc ⊢
      omega

/-- **Flight square lemma**: a lone king on `e` checked by a knight on `n`, with the enemy king
on `a` not adjacent, has a neighbouring square not adjacent to `a` and not attacked by the
knight (an orthogonal neighbour has the colour of `n`, which the knight does not attack, and
the enemy king cannot cover two perpendicular orthogonal neighbours without touching `e`). -/
theorem knk_flight {a e n : Square} (hae : kingAdj a e = false) (ha : a ≠ e)
    (hn : knightAdj e n = true) :
    ∃ t, kingAdj e t = true ∧ kingAdj t a = false ∧ t ≠ a ∧ knightAdj t n = false := by
  have he := e.isLt
  rcases Nat.lt_or_ge (e.val % 8) 7 with hf | hf <;> rcases Nat.lt_or_ge (e.val / 8) 7 with hr | hr
  · exact knk_flight_of (t₁ := ⟨e.val + 1, by omega⟩) (t₂ := ⟨e.val + 8, by omega⟩) hae ha hn
      (by simp only; omega) (by simp only; omega)
  · exact knk_flight_of (t₁ := ⟨e.val + 1, by omega⟩) (t₂ := ⟨e.val - 8, by omega⟩) hae ha hn
      (by simp only; omega) (by simp only; omega)
  · exact knk_flight_of (t₁ := ⟨e.val - 1, by omega⟩) (t₂ := ⟨e.val + 8, by omega⟩) hae ha hn
      (by simp only; omega) (by simp only; omega)
  · exact knk_flight_of (t₁ := ⟨e.val - 1, by omega⟩) (t₂ := ⟨e.val - 8, by omega⟩) hae ha hn
      (by simp only; omega) (by simp only; omega)

/-- Two bare kings, colour-generic: the king of `c` on `a`, the king of `c.other` on `e`. -/
def kk2 (c : Color) (a e : Square) : Board := fun s =>
  if s = a then some ⟨c, .king⟩ else if s = e then some ⟨c.other, .king⟩ else none

/-- `kk2` is `kk` with the kings in the right order. -/
theorem kk2_eq {c : Color} {a e : Square} (hae : a ≠ e) :
    kk2 c a e = match c with
      | .white => kk a e
      | .black => kk e a := by
  funext s
  cases c
  · rfl
  · simp only [kk2, kk, Color.other]
    split_ifs <;> simp_all

/-- A `kk2` board with the side `c.other` not in check satisfies the bare-kings invariant. -/
theorem KKInv.of_kk2 {p : Position} {c : Color} {a e : Square} (hae : a ≠ e)
    (hb : p.board = kk2 c a e) (hc : inCheck p.board c.other = false) : KKInv p := by
  rw [hb, kk2_eq hae] at hc
  rw [kk2_eq hae] at hb
  cases c
  · rw [Color.other, inCheck_kk_black hae, kingAdj_comm] at hc
    exact ⟨a, e, hae, hb, hc⟩
  · rw [Color.other, inCheck_kk_white (Ne.symm hae)] at hc
    exact ⟨e, a, Ne.symm hae, hb, hc⟩

/-- **The king-and-knight invariant**: the board is `knb c a e n` with three distinct squares,
and the side not to move is not in check. -/
def KNInv (p : Position) : Prop :=
  ∃ c a e n, a ≠ e ∧ n ≠ a ∧ n ≠ e ∧ p.board = knb c a e n ∧
    inCheck p.board p.turn.other = false

/-- Under the king-and-knight invariant there is no checkmate. -/
theorem KNInv.not_checkmate {p : Position} (h : KNInv p) : isCheckmate p = false := by
  obtain ⟨c, a, e, n, hae, hna, hne, hb, hchk⟩ := h
  rcases Color.eq_or_eq_other p.turn c with ht | ht
  · rw [hb, ht, inCheck_knb_lone hae hna hne, Bool.or_eq_false_iff] at hchk
    have : inCheck p.board p.turn = false := by
      rw [hb, ht, inCheck_knb_strong hae, kingAdj_comm]
      exact hchk.1
    simp [isCheckmate, this]
  · rw [hb, ht, Color.other_other, inCheck_knb_strong hae] at hchk
    cases hc : inCheck p.board p.turn
    · simp [isCheckmate, hc]
    · rw [hb, ht, inCheck_knb_lone hae hna hne, kingAdj_comm, hchk, Bool.false_or] at hc
      obtain ⟨t, het, hta, hta', htn⟩ := knk_flight hchk hae hc
      have hmem : (⟨e, t, none⟩ : Move) ∈ legalMoves p := by
        have hte : t ≠ e := fun h => by
          rw [h, kingAdj_iff] at het; exact het.1 rfl
        have he : p.board e = some ⟨p.turn, .king⟩ := by rw [hb, ht, knb_ok hae]
        have hpb := play_board_simple (m := ⟨e, t, none⟩) he (by simp) rfl (fun _ => het)
        simp only [legalMoves, List.mem_filter, Bool.not_eq_true']
        refine ⟨kingMove_mem_pseudoMoves he het ?_, ?_⟩
        · intro pc hpc
          rw [hb] at hpc
          rw [ht]
          have := Color.other_ne c
          have := Ne.symm this
          unfold knb at hpc
          split_ifs at hpc <;> simp only [Option.some.injEq] at hpc <;> subst hpc <;>
            simp_all
        · rw [hpb, ht]
          simp only
          by_cases htn' : t = n
          · subst htn'
            have hbd : (fun x => if x = t then p.board e else if x = e then none else p.board x)
                = kk2 c a t := by
              funext x; simp only [hb, knb, kk2]; split_ifs <;> simp_all
            rw [hbd, kk2_eq (Ne.symm hta')]
            cases c
            · rw [Color.other, inCheck_kk_black (Ne.symm hta')]; exact hta
            · rw [Color.other, inCheck_kk_white hta']; exact hta
          · have hbd : (fun x => if x = t then p.board e else if x = e then none else p.board x)
                = knb c a t n := by
              funext x; simp only [hb, knb]; split_ifs <;> simp_all
            rw [hbd, inCheck_knb_lone (Ne.symm hta') hna (Ne.symm htn'), hta, htn]
            rfl
      cases hl : legalMoves p with
      | nil => rw [hl] at hmem; simp at hmem
      | cons _ _ => simp [isCheckmate, hl]

/-- A legal move from a king-and-knight position leads to a king-and-knight position or (after
the capture of the knight) to a bare-kings position. -/
theorem KNInv.play {p : Position} {m : Move} (h : KNInv p) (hm : m ∈ legalMoves p) :
    KKInv (Chess.play p m) ∨ KNInv (Chess.play p m) := by
  obtain ⟨c, a, e, n, hae, hna, hne, hb, hchk⟩ := h
  simp only [legalMoves, List.mem_filter, Bool.not_eq_true'] at hm
  obtain ⟨hps, hlg⟩ := hm
  have hkn : ∀ s pc, p.board s = some pc → pc.kind = .king ∨ pc.kind = .knight :=
    fun s pc h => knb_kind (hb ▸ h)
  obtain ⟨hpr, hmv, hdst⟩ := mem_pseudoMoves_KN hkn hps
  have hco := Color.other_ne c
  have hco' := Ne.symm hco
  have htn : (Chess.play p m).turn.other = p.turn := by rw [turn_play, Color.other_other]
  rcases Color.eq_or_eq_other p.turn c with ht | ht
  · rw [hb, ht, inCheck_knb_lone hae hna hne, Bool.or_eq_false_iff] at hchk
    rcases hmv with ⟨hs, had⟩ | ⟨hs, had⟩
    · -- the strong king moves
      have hpb := play_board_simple hs (by simp) hpr (fun _ => had)
      rw [hb, ht, knb_ck] at hs
      have hda : m.dst ≠ a := fun h => by
        rw [hs, h, kingAdj_iff] at had; exact had.1 rfl
      have hde : m.dst ≠ e := fun h => by
        rw [hs, h, kingAdj_comm, hchk.1] at had; exact Bool.false_ne_true had
      have hdn : m.dst ≠ n := fun h => by
        refine hdst ⟨c, .knight⟩ ?_ ht.symm
        rw [hb, h, knb_cn hna hne]
      have hbd : (fun t => if t = m.dst then p.board m.src else if t = m.src then none else
          p.board t) = knb c m.dst e n := by
        funext x; simp only [hb, knb]; split_ifs <;> simp_all
      refine Or.inr ⟨c, m.dst, e, n, hde, Ne.symm hdn, hne, hpb.trans hbd, ?_⟩
      rw [htn, hpb, hbd]
      rw [hpb, hbd] at hlg
      exact hlg
    · -- the knight moves
      have hpb := play_board_simple hs (by simp) hpr (by simp)
      rw [hb, ht, knb_cn hna hne] at hs
      have hda : m.dst ≠ a := fun h => by
        refine hdst ⟨c, .king⟩ ?_ ht.symm
        rw [hb, h, knb_ck]
      have hde : m.dst ≠ e := fun h => by
        rw [hs, h, knightAdj_comm, hchk.2] at had; exact Bool.false_ne_true had
      have hdn : m.dst ≠ n := fun h => by
        rw [hs, h] at had; have := knightAdj_parity had; exact this rfl
      have hbd : (fun t => if t = m.dst then p.board m.src else if t = m.src then none else
          p.board t) = knb c a e m.dst := by
        funext x; simp only [hb, knb]; split_ifs <;> simp_all
      refine Or.inr ⟨c, a, e, m.dst, hae, hda, hde, hpb.trans hbd, ?_⟩
      rw [htn, hpb, hbd]
      rw [hpb, hbd] at hlg
      exact hlg
  · rw [hb, ht, Color.other_other, inCheck_knb_strong hae] at hchk
    rcases hmv with ⟨hs, had⟩ | ⟨hs, had⟩
    · -- the lone king moves
      have hpb := play_board_simple hs (by simp) hpr (fun _ => had)
      rw [hb, ht, knb_ok hae] at hs
      have hde : m.dst ≠ e := fun h => by
        rw [hs, h, kingAdj_iff] at had; exact had.1 rfl
      have hda : m.dst ≠ a := fun h => by
        rw [hs, h, kingAdj_comm, hchk] at had; exact Bool.false_ne_true had
      by_cases hdn : m.dst = n
      · have hbd : (fun t => if t = m.dst then p.board m.src else if t = m.src then none else
            p.board t) = kk2 c a m.dst := by
          funext x; simp only [hb, knb, kk2]; split_ifs <;> simp_all
        refine Or.inl (KKInv.of_kk2 (Ne.symm hda) (hpb.trans hbd) ?_)
        rw [hpb]
        rw [hpb, ht] at hlg
        exact hlg
      · have hbd : (fun t => if t = m.dst then p.board m.src else if t = m.src then none else
            p.board t) = knb c a m.dst n := by
          funext x; simp only [hb, knb]; split_ifs <;> simp_all
        refine Or.inr ⟨c, a, m.dst, n, Ne.symm hda, hna, Ne.symm hdn, hpb.trans hbd, ?_⟩
        rw [htn, ht]
        rw [ht] at hlg
        exact hlg
    · rw [hb, ht] at hs
      exact absurd hs (knb_on _)

/-- The dead-position invariant: bare kings, or king and knight against king. -/
def DInv (p : Position) : Prop := KKInv p ∨ KNInv p

/-- A position satisfying `DInv` is dead. -/
theorem DInv.isDead {p : Position} (h : DInv p) : IsDead p := by
  intro ms
  induction ms generalizing p with
  | nil =>
    intro q hq
    simp only [playLegal, Option.some.injEq] at hq
    subst hq
    rcases h with h | h
    · exact h.not_checkmate
    · exact h.not_checkmate
  | cons m ms ih =>
    intro q hq
    simp only [playLegal] at hq
    split_ifs at hq with hl
    have hm := (isLegal_iff _ _).1 hl
    rcases h with h | h
    · exact ih (Or.inl (h.play hm)) q hq
    · exact ih (h.play hm) q hq

/-- Every piece on the board is a king or the piece `pc`. -/
def kingsAnd (pc : Piece) (b : Board) : Bool :=
  allSquares.all fun s => match b s with
    | some q => q.kind == .king || q == pc
    | none => true

/-- Specification of `kingsAnd`. -/
theorem kingsAnd_spec {pc : Piece} {b : Board} (h : kingsAnd pc b = true) {s : Square}
    {q : Piece} (hs : b s = some q) : q.kind = .king ∨ q = pc := by
  simp only [kingsAnd, List.all_eq_true] at h
  have := h s (mem_allSquares s)
  simpa [hs] using this

/-- In a well-formed position each player has exactly one king. -/
theorem king_unique_of_wellFormed {p : Position} (hw : wellFormed p = true) (c : Color) :
    ∃ s, ∀ u, p.board u = some ⟨c, .king⟩ ↔ u = s := by
  simp only [wellFormed, Bool.and_eq_true, beq_iff_eq] at hw
  cases c
  · exact countPiece_eq_one hw.1.1.1.1
  · exact countPiece_eq_one hw.1.1.1.2

/-- A well-formed position with two kings and exactly one knight (of colour `c`) satisfies the
king-and-knight invariant. -/
theorem KNInv.of_wellFormed {p : Position} (hw : wellFormed p = true) (c : Color)
    (hm : kingsAnd ⟨c, .knight⟩ p.board = true) (hn : countPiece p.board ⟨c, .knight⟩ = 1) :
    KNInv p := by
  obtain ⟨a, ha⟩ := king_unique_of_wellFormed hw c
  obtain ⟨e, he⟩ := king_unique_of_wellFormed hw c.other
  obtain ⟨n, hn'⟩ := countPiece_eq_one hn
  have hco := Color.other_ne c
  have hae : a ≠ e := by
    rintro rfl
    have h1 := (ha a).2 rfl
    rw [(he a).2 rfl] at h1
    exact hco (by simpa using h1)
  have hna : n ≠ a := by
    rintro rfl
    have h1 := (ha n).2 rfl
    rw [(hn' n).2 rfl] at h1
    simp at h1
  have hne : n ≠ e := by
    rintro rfl
    have h1 := (he n).2 rfl
    rw [(hn' n).2 rfl] at h1
    simp at h1
  have hb : p.board = knb c a e n := by
    funext s
    unfold knb
    split_ifs with h1 h2 h3
    · exact (ha s).2 h1
    · exact (he s).2 h2
    · exact (hn' s).2 h3
    · cases hs : p.board s with
      | none => rfl
      | some q =>
        rcases kingsAnd_spec hm hs with hk | hk
        · obtain ⟨qc, qk⟩ := q
          simp only at hk
          subst hk
          rcases Color.eq_or_eq_other qc c with rfl | rfl
          · exact absurd ((ha s).1 hs) h1
          · exact absurd ((he s).1 hs) h2
        · subst hk
          exact absurd ((hn' s).1 hs) h3
  have hchk : inCheck p.board p.turn.other = false := by
    simp only [wellFormed, Bool.and_eq_true, Bool.not_eq_true'] at hw
    exact hw.1.2
  exact ⟨c, a, e, n, hae, hna, hne, hb, hchk⟩

/-- **King and knight against king is dead** (FIDE 5.2.2): a well-formed position whose pieces
are the two kings and exactly one knight (of either colour `c`) is dead. Castling flags and the
halfmove clock are arbitrary (castling needs a rook). -/
theorem dead_KNK (p : Position) (c : Color) (hw : wellFormed p = true)
    (hm : kingsAnd ⟨c, .knight⟩ p.board = true) (hn : countPiece p.board ⟨c, .knight⟩ = 1) :
    IsDead p :=
  DInv.isDead (Or.inr (KNInv.of_wellFormed hw c hm hn))

/-! ### Fixtures -/

/-- White: king e1; Black: king e8; White to move. -/
def kkPos : Position :=
  Position.ofList [(sq 4 1, ⟨.white, .king⟩), (sq 4 8, ⟨.black, .king⟩)] .white

/-- `K` vs `K` is dead (concrete instance of `dead_KK`). -/
theorem kkPos_dead : IsDead kkPos := dead_KK _ (by kernel_fact) (by kernel_fact)

/-- Stray castling flags and a large halfmove clock do not matter. -/
theorem kkPos_flags_dead : IsDead { kkPos with castling := .all, halfmove := 120 } :=
  dead_KK _ (by kernel_fact) (by kernel_fact)

/-- Rejected fixture: adjacent kings are not well formed (so `dead_KK` does not apply). -/
theorem adjacent_kings_not_wellFormed :
    wellFormed (Position.ofList [(sq 4 1, ⟨.white, .king⟩), (sq 4 2, ⟨.black, .king⟩)] .white)
      = false := by kernel_fact

/-- White: king e1, knight b1; Black: king e8; Black to move. -/
def knkPos : Position :=
  Position.ofList [(sq 4 1, ⟨.white, .king⟩), (sq 1 1, ⟨.white, .knight⟩),
    (sq 4 8, ⟨.black, .king⟩)] .black

/-- `KN` vs `K` is dead (concrete instance of `dead_KNK`). -/
theorem knkPos_dead : IsDead knkPos := dead_KNK _ .white (by kernel_fact) (by kernel_fact)
  (by kernel_fact)

/-- Black: king a8, knight c7 (no check); White: king a6; White to move. The lone king is
white here. -/
def knkPosBlack : Position :=
  Position.ofList [(sq 0 8, ⟨.black, .king⟩), (sq 2 7, ⟨.black, .knight⟩),
    (sq 0 6, ⟨.white, .king⟩)] .white

/-- `K` vs `KN` with the knight on the black side is dead. -/
theorem knkPosBlack_dead : IsDead knkPosBlack :=
  dead_KNK _ .black (by kernel_fact) (by kernel_fact) (by kernel_fact)

/-- Black: king h8; White: king g6, queen a7; White to move. -/
def kqkFixture : Position :=
  Position.ofList [(sq 7 8, ⟨.black, .king⟩), (sq 6 6, ⟨.white, .king⟩),
    (sq 0 7, ⟨.white, .queen⟩)] .white

/-- Rejected fixture: the `KQK` position is not a kings-only position. -/
theorem kqkPos_not_onlyKings : onlyKings kqkFixture.board = false := by kernel_fact

/-- Rejected fixture: the queen is not a knight, so `dead_KNK` does not apply to `kqkFixture`. -/
theorem kqkPos_not_kingsAndKnight : kingsAnd ⟨.white, .knight⟩ kqkFixture.board = false := by
  kernel_fact

/-- **A `KQK` position is not dead**: White mates in one (`Qa7–g7#`). Guards against an
over-broad `IsDead`. -/
theorem not_dead_KQK_example : ¬ IsDead kqkFixture :=
  (forcesMateB_sound .white 1 kqkFixture (by kernel_fact)).not_isDead

end LeanTheory.Chess
