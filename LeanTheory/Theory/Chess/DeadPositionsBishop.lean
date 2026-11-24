/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Chess.DeadPositions

/-!
# Dead positions: king and bishop against king

Note `N-07`, continuing `Theory/Chess/DeadPositions` (bare kings and `KNK`). FIDE Article 5.2.2
calls a position *dead* when no sequence of legal moves leads to a checkmate (`IsDead`). As for
the knight, the proof is by an invariant closed under legal moves that excludes checkmate,
reasoning symbolically about `pseudoMoves`, `play` and `inCheck` (no enumeration, no `decide`).

* `dead_KBK`: every well-formed position with the two kings and exactly one bishop (of either
  colour, on either square colour) is dead. Invariant `DBInv := KKInv ∨ KBInv`, where `KBInv`
  says the board is `kbb c a e n` (king of `c` on `a`, lone king on `e`, bishop of `c` on `n`)
  and the side not to move is not in check.
* Diagonal-colour lemma `firstOnRay_diag`: the first piece met along a diagonal ray stands on a
  square of the start square's colour (`squareParity`).
* Ray-reversal lemma `firstOnRay_of_mem_rayTargets`: if a slider can move to an occupied square
  `t`, then looking back from `t` in the opposite direction first meets the slider. Hence the
  bishop never captures the lone king (the king would already be in check).
* Flight-square lemma `kbk_flight`: a king not next to the enemy king has an orthogonal
  neighbour, of the other colour, not next to the enemy king; a bishop checking the king stands
  on the king's colour (`kbb_check_parity`), so it does not attack that neighbour.
* Fixtures: dead `KBK` positions with a white bishop, a black bishop and a checking bishop
  (`kernel_fact` side conditions), and rejected fixtures (two bishops; a queen).

Scope: castling flags, the en passant field and the halfmove clock are arbitrary.
-/

@[expose] public section

namespace LeanTheory.Chess

/-! ### Square colours and diagonal rays -/

/-- The colour of a square as a parity: `0` for dark squares (`a1`), `1` for light ones. -/
def squareParity (s : Square) : Nat := (s.val % 8 + s.val / 8) % 2

/-- A diagonal step keeps the colour of the square. -/
theorem shift_bishopDir_parity {s t : Square} {d : Int × Int} (hd : d ∈ bishopDirs)
    (h : s.shift d.1 d.2 = some t) : squareParity t = squareParity s := by
  simp only [bishopDirs, List.mem_cons, List.not_mem_nil, or_false] at hd
  rw [shift_eq_some] at h
  simp only [squareParity, Square.file, Square.rank] at h ⊢
  rcases hd with rfl | rfl | rfl | rfl <;> dsimp only at h <;> omega

/-- The opposite of a bishop direction is a bishop direction. -/
theorem neg_mem_bishopDirs {d : Int × Int} (hd : d ∈ bishopDirs) :
    ((-d.1, -d.2) : Int × Int) ∈ bishopDirs := by
  simp only [bishopDirs, List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
  rcases hd with rfl | rfl | rfl | rfl <;> simp

/-- **Diagonal-colour lemma**: the piece met first along a diagonal ray stands on a square of the
colour of the start square. -/
theorem firstOnRay_diag {b : Board} {d : Int × Int} (hd : d ∈ bishopDirs) :
    ∀ {k : Nat} {s : Square} {pc : Piece}, firstOnRay b d.1 d.2 k s = some pc →
      ∃ t, b t = some pc ∧ squareParity t = squareParity s := by
  intro k
  induction k with
  | zero => intro s pc h; simp [firstOnRay] at h
  | succ k ih =>
    intro s pc h
    simp only [firstOnRay] at h
    split at h
    · simp at h
    · next t ht =>
      split at h
      · next p hp =>
        refine ⟨t, ?_, shift_bishopDir_parity hd ht⟩
        simp_all
      · obtain ⟨u, hu, hpu⟩ := ih h
        exact ⟨u, hu, hpu.trans (shift_bishopDir_parity hd ht)⟩

/-- The first piece on a ray starting *at* `s` (inclusive), then `n` further steps. -/
def firstFrom (b : Board) (df dr : Int) (n : Nat) (s : Square) : Option Piece :=
  match b s with
  | some p => some p
  | none => firstOnRay b df dr n s

/-- Ray reversal (general form): if a slider on `s` reaches the occupied square `t` along
`(df, dr)`, then looking back from `t` along `(-df, -dr)` passes empty squares only, until `s`. -/
theorem rayTargets_reverse {b : Board} {c : Color} {df dr : Int} :
    ∀ {k : Nat} {s t : Square}, t ∈ rayTargets b c df dr k s → b t ≠ none →
      ∀ M, ∃ N, M ≤ N ∧ firstOnRay b (-df) (-dr) (M + k) t = firstFrom b (-df) (-dr) N s := by
  intro k
  induction k with
  | zero => intro s t ht; simp [rayTargets] at ht
  | succ k ih =>
    intro s t ht hbt M
    simp only [rayTargets] at ht
    split at ht
    · simp at ht
    · next u hu =>
      split at ht
      · next hbu =>
        rcases List.mem_cons.1 ht with rfl | ht'
        · exact absurd hbu hbt
        · obtain ⟨N, hN, h⟩ := ih ht' hbt (M + 1)
          obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
          refine ⟨N', by omega, ?_⟩
          rw [show M + (k + 1) = M + 1 + k by omega, h]
          simp only [firstFrom, hbu, firstOnRay, shift_neg hu]
          rfl
      · next p hp =>
        split_ifs at ht
        · simp at ht
        obtain rfl : t = u := List.mem_singleton.1 ht
        refine ⟨M + k, by omega, ?_⟩
        rw [show M + (k + 1) = (M + k) + 1 by omega]
        simp only [firstOnRay, shift_neg hu, firstFrom]
        rfl

/-- **Ray-reversal lemma**: if a slider on `s` can move to the occupied square `t` along
`(df, dr)`, then the first piece seen from `t` along `(-df, -dr)` is the slider. -/
theorem firstOnRay_of_mem_rayTargets {b : Board} {c : Color} {df dr : Int} {s t : Square}
    {pc : Piece} (hs : b s = some pc) (ht : t ∈ rayTargets b c df dr 7 s) (hbt : b t ≠ none) :
    firstOnRay b (-df) (-dr) 7 t = some pc := by
  obtain ⟨N, -, h⟩ := rayTargets_reverse ht hbt 0
  rw [Nat.zero_add] at h
  rw [h]
  simp [firstFrom, hs]

/-- A slider never moves onto a piece of its own colour. -/
theorem mem_rayTargets_color {b : Board} {c : Color} {df dr : Int} :
    ∀ {k : Nat} {s t : Square}, t ∈ rayTargets b c df dr k s →
      ∀ pc, b t = some pc → pc.color ≠ c := by
  intro k
  induction k with
  | zero => intro s t ht; simp [rayTargets] at ht
  | succ k ih =>
    intro s t ht pc hpc
    simp only [rayTargets] at ht
    split at ht
    · simp at ht
    · next u hu =>
      split at ht
      · next hbu =>
        rcases List.mem_cons.1 ht with rfl | ht'
        · simp_all
        · exact ih ht' pc hpc
      · next p hp =>
        split_ifs at ht with hc
        · simp at ht
        obtain rfl : t = u := List.mem_singleton.1 ht
        rw [hp] at hpc
        cases hpc
        exact hc

/-! ### Attacks on a board with kings and bishops -/

/-- On a board with kings and bishops only, a square is attacked exactly when an enemy king is
a king step away or the first piece on some diagonal ray is an enemy bishop. -/
theorem attackedBy_KB {b : Board}
    (hb : ∀ s pc, b s = some pc → pc.kind = .king ∨ pc.kind = .bishop) (c : Color) (s : Square) :
    attackedBy b c s = true ↔ pieceAtOffsets b ⟨c, .king⟩ s kingDeltas = true ∨
      ∃ d ∈ bishopDirs, firstOnRay b d.1 d.2 7 s = some ⟨c, .bishop⟩ := by
  have hray : ∀ df dr pc, firstOnRay b df dr 7 s = some pc →
      pc.kind = .king ∨ pc.kind = .bishop := by
    intro df dr pc h
    obtain ⟨t, ht⟩ := firstOnRay_some h
    exact hb _ _ ht
  unfold attackedBy
  rw [pieceAtOffsets_eq_false (pc := ⟨c, .knight⟩) (fun t ht => by simpa using hb _ _ ht),
    pieceAtOffsets_eq_false (pc := ⟨c, .pawn⟩) (fun t ht => by simpa using hb _ _ ht)]
  simp only [Bool.false_or, Bool.or_false, Bool.or_eq_true, List.any_eq_true]
  constructor
  · rintro ((h | ⟨d, _, hd⟩) | ⟨d, hd, h⟩)
    · exact Or.inl h
    · split at hd
      · next p hp =>
        obtain ⟨pc, pk⟩ := p
        rcases hray _ _ _ hp with h | h <;> simp only at h <;> subst h <;> simp at hd
      · simp at hd
    · split at h
      · next p hp =>
        obtain ⟨pc, pk⟩ := p
        rcases hray _ _ _ hp with h' | h' <;> simp only at h' <;> subst h'
        · simp at h
        · obtain rfl : pc = c := by simpa using h
          exact Or.inr ⟨d, hd, hp⟩
      · simp at h
  · rintro (h | ⟨d, hd, h⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inr ⟨d, hd, by rw [h]; simp⟩

/-- The board with the king of `c` on `a`, the king of `c.other` on `e`, the bishop of `c` on
`n` and nothing else. -/
def kbb (c : Color) (a e n : Square) : Board := fun s =>
  if s = a then some ⟨c, .king⟩ else if s = e then some ⟨c.other, .king⟩
  else if s = n then some ⟨c, .bishop⟩ else none

/-- `kbb` has only kings and bishops. -/
theorem kbb_kind {c : Color} {a e n s : Square} {pc : Piece} (h : kbb c a e n s = some pc) :
    pc.kind = .king ∨ pc.kind = .bishop := by
  unfold kbb at h; split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;> simp

/-- The king of `c` stands exactly on `a`. -/
theorem kbb_ck {c : Color} {a e n s : Square} : kbb c a e n s = some ⟨c, .king⟩ ↔ s = a := by
  have := Color.other_ne c
  unfold kbb; split_ifs <;> simp_all

/-- The king of `c.other` stands exactly on `e`. -/
theorem kbb_ok {c : Color} {a e n s : Square} (hae : a ≠ e) :
    kbb c a e n s = some ⟨c.other, .king⟩ ↔ s = e := by
  have := Color.other_ne c
  unfold kbb; split_ifs <;> simp_all [eq_comm]

/-- The bishop of `c` stands exactly on `n`. -/
theorem kbb_cb {c : Color} {a e n s : Square} (hna : n ≠ a) (hne : n ≠ e) :
    kbb c a e n s = some ⟨c, .bishop⟩ ↔ s = n := by
  have := Ne.symm hna
  have := Ne.symm hne
  unfold kbb; split_ifs <;> simp_all

/-- The lone side has no bishop. -/
theorem kbb_ob {c : Color} {a e n : Square} (s : Square) :
    kbb c a e n s ≠ some ⟨c.other, .bishop⟩ := by
  have := Color.other_ne c
  unfold kbb; split_ifs <;> simp_all [eq_comm]

/-- The side with the bishop is in check iff the kings are adjacent. -/
theorem inCheck_kbb_strong {c : Color} {a e n : Square} (hae : a ≠ e) :
    inCheck (kbb c a e n) c = kingAdj a e := by
  unfold inCheck
  rw [kingSquare_unique (fun _ => kbb_ck)]
  simp only
  rw [Bool.eq_iff_iff, attackedBy_KB (fun _ _ => kbb_kind), pieceAtOffsets_unique
    (fun _ => kbb_ok hae)]
  constructor
  · rintro (h | ⟨d, -, h⟩)
    · exact h
    · obtain ⟨t, ht⟩ := firstOnRay_some h
      exact absurd ht (kbb_ob t)
  · exact fun h => Or.inl h

/-- The lone king is in check iff it is adjacent to the enemy king or the first piece on one of
its diagonal rays is the bishop. -/
theorem inCheck_kbb_lone {c : Color} {a e n : Square} (hae : a ≠ e) :
    inCheck (kbb c a e n) c.other = true ↔ kingAdj e a = true ∨
      ∃ d ∈ bishopDirs, firstOnRay (kbb c a e n) d.1 d.2 7 e = some ⟨c, .bishop⟩ := by
  unfold inCheck
  rw [kingSquare_unique (fun _ => kbb_ok hae)]
  simp only [Color.other_other]
  rw [attackedBy_KB (fun _ _ => kbb_kind), pieceAtOffsets_unique (fun _ => kbb_ck)]
  rfl

/-- A lone king in check by the bishop (not by the king) stands on the bishop's colour. -/
theorem kbb_check_parity {c : Color} {a e n : Square} (hae : a ≠ e) (hna : n ≠ a) (hne : n ≠ e)
    (hk : kingAdj e a = false) (hc : inCheck (kbb c a e n) c.other = true) :
    squareParity n = squareParity e := by
  rcases (inCheck_kbb_lone hae).1 hc with h | ⟨d, hd, h⟩
  · rw [hk] at h; exact absurd h Bool.false_ne_true
  · obtain ⟨u, hu, hp⟩ := firstOnRay_diag hd h
    rw [kbb_cb hna hne] at hu
    rw [← hu, hp]

/-- A lone king that is not next to the enemy king and stands on the other colour than the
bishop is not in check. -/
theorem kbb_lone_safe {c : Color} {a e n : Square} (hae : a ≠ e) (hna : n ≠ a) (hne : n ≠ e)
    (hk : kingAdj e a = false) (hp : squareParity n ≠ squareParity e) :
    inCheck (kbb c a e n) c.other = false := by
  cases hc : inCheck (kbb c a e n) c.other
  · rfl
  · exact absurd (kbb_check_parity hae hna hne hk hc) hp

/-! ### The flight square -/

/-- Geometric core with explicit candidates: given a horizontal neighbour `t₁` and a vertical
neighbour `t₂` of the lone king `e`, one of them is a flight square of the other colour. -/
theorem kbk_flight_of {a e t₁ t₂ : Square} (hae : kingAdj a e = false) (ha : a ≠ e)
    (h₁ : t₁.val / 8 = e.val / 8 ∧ (t₁.val % 8 = e.val % 8 + 1 ∨ t₁.val % 8 + 1 = e.val % 8))
    (h₂ : t₂.val % 8 = e.val % 8 ∧ (t₂.val / 8 = e.val / 8 + 1 ∨ t₂.val / 8 + 1 = e.val / 8)) :
    ∃ t, kingAdj e t = true ∧ kingAdj t a = false ∧ t ≠ a ∧
      squareParity t ≠ squareParity e := by
  have hae' : ¬ (kingAdj a e = true) := by simp [hae]
  rw [kingAdj_iff] at hae'
  simp only [ne_eq, Fin.ext_iff] at hae' ha
  have adj : ∀ t : Square, (t.val / 8 = e.val / 8 ∧
      (t.val % 8 = e.val % 8 + 1 ∨ t.val % 8 + 1 = e.val % 8)) ∨
      (t.val % 8 = e.val % 8 ∧ (t.val / 8 = e.val / 8 + 1 ∨ t.val / 8 + 1 = e.val / 8)) →
      kingAdj e t = true := by
    intro t ht
    rw [kingAdj_iff]
    simp only [ne_eq, Fin.ext_iff]
    omega
  by_cases hc : kingAdj t₁ a = false ∧ t₁ ≠ a
  · exact ⟨t₁, adj _ (Or.inl h₁), hc.1, hc.2, by simp only [squareParity]; omega⟩
  · refine ⟨t₂, adj _ (Or.inr h₂), ?_, ?_, by simp only [squareParity]; omega⟩
    · rw [Bool.eq_false_iff, ne_eq, kingAdj_iff]
      rw [Bool.eq_false_iff, ne_eq, kingAdj_iff] at hc
      simp only [ne_eq, Fin.ext_iff] at hc ⊢
      omega
    · rw [Bool.eq_false_iff, ne_eq, kingAdj_iff] at hc
      simp only [ne_eq, Fin.ext_iff] at hc ⊢
      omega

/-- **Flight square lemma for the bishop**: a king on `e` with the enemy king on `a` not adjacent
has a neighbouring square of the other colour that is not adjacent to `a`. -/
theorem kbk_flight {a e : Square} (hae : kingAdj a e = false) (ha : a ≠ e) :
    ∃ t, kingAdj e t = true ∧ kingAdj t a = false ∧ t ≠ a ∧
      squareParity t ≠ squareParity e := by
  have he := e.isLt
  rcases Nat.lt_or_ge (e.val % 8) 7 with hf | hf <;> rcases Nat.lt_or_ge (e.val / 8) 7 with hr | hr
  · exact kbk_flight_of (t₁ := ⟨e.val + 1, by omega⟩) (t₂ := ⟨e.val + 8, by omega⟩) hae ha
      (by simp only; omega) (by simp only; omega)
  · exact kbk_flight_of (t₁ := ⟨e.val + 1, by omega⟩) (t₂ := ⟨e.val - 8, by omega⟩) hae ha
      (by simp only; omega) (by simp only; omega)
  · exact kbk_flight_of (t₁ := ⟨e.val - 1, by omega⟩) (t₂ := ⟨e.val + 8, by omega⟩) hae ha
      (by simp only; omega) (by simp only; omega)
  · exact kbk_flight_of (t₁ := ⟨e.val - 1, by omega⟩) (t₂ := ⟨e.val - 8, by omega⟩) hae ha
      (by simp only; omega) (by simp only; omega)

/-! ### Moves on a board with kings and bishops -/

/-- On a board with kings and bishops only, a pseudo-legal move is a plain king step or a
diagonal slide of a bishop of the side to move, onto a square without a piece of its own. -/
theorem mem_pseudoMoves_KB {p : Position}
    (hb : ∀ s pc, p.board s = some pc → pc.kind = .king ∨ pc.kind = .bishop) {m : Move}
    (hm : m ∈ pseudoMoves p) :
    m.promo = none ∧
      ((p.board m.src = some ⟨p.turn, .king⟩ ∧ kingAdj m.src m.dst = true) ∨
        (p.board m.src = some ⟨p.turn, .bishop⟩ ∧
          ∃ d ∈ bishopDirs, m.dst ∈ rayTargets p.board p.turn d.1 d.2 7 m.src)) ∧
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
  · next pc hs =>
    split_ifs at hm with hc
    · obtain ⟨c, k⟩ := pc
      simp only at hc
      subst hc
      rcases hb _ _ hs with hk | hk <;> simp only at hk <;> subst hk <;>
        simp only [pieceMoves, List.mem_map] at hm <;>
        obtain ⟨t, ht, rfl⟩ := hm
      · obtain ⟨⟨d, hd, hu⟩, hc⟩ := mem_stepTargets.1 ht
        refine ⟨rfl, Or.inl ⟨hs, ?_⟩, hc⟩
        simp only [kingAdj, List.any_eq_true, beq_iff_eq]
        exact ⟨d, hd, hu⟩
      · obtain ⟨d, hd, ht⟩ := List.mem_flatMap.1 ht
        exact ⟨rfl, Or.inr ⟨hs, d, hd, ht⟩, mem_rayTargets_color ht⟩
    · simp at hm
  · simp at hm

/-! ### The king-and-bishop invariant -/

/-- **The king-and-bishop invariant**: the board is `kbb c a e n` with three distinct squares,
and the side not to move is not in check. -/
def KBInv (p : Position) : Prop :=
  ∃ c a e n, a ≠ e ∧ n ≠ a ∧ n ≠ e ∧ p.board = kbb c a e n ∧
    inCheck p.board p.turn.other = false

/-- If the lone king is not in check, the kings are not adjacent. -/
theorem kingAdj_of_lone_safe {c : Color} {a e n : Square} (hae : a ≠ e)
    (h : inCheck (kbb c a e n) c.other = false) : kingAdj e a = false := by
  cases hk : kingAdj e a
  · rfl
  · rw [((inCheck_kbb_lone hae).2 (Or.inl hk))] at h
    exact Bool.noConfusion h

/-- Under the king-and-bishop invariant there is no checkmate. -/
theorem KBInv.not_checkmate {p : Position} (h : KBInv p) : isCheckmate p = false := by
  obtain ⟨c, a, e, n, hae, hna, hne, hb, hchk⟩ := h
  rcases Color.eq_or_eq_other p.turn c with ht | ht
  · rw [hb, ht] at hchk
    have : inCheck p.board p.turn = false := by
      rw [hb, ht, inCheck_kbb_strong hae, kingAdj_comm]
      exact kingAdj_of_lone_safe hae hchk
    simp [isCheckmate, this]
  · rw [hb, ht, Color.other_other, inCheck_kbb_strong hae] at hchk
    cases hc : inCheck p.board p.turn
    · simp [isCheckmate, hc]
    · rw [hb, ht] at hc
      have hka : kingAdj e a = false := by rw [kingAdj_comm]; exact hchk
      have hpar := kbb_check_parity hae hna hne hka hc
      obtain ⟨t, het, hta, hta', htp⟩ := kbk_flight hchk hae
      have hte : t ≠ e := fun h => by
        rw [h, kingAdj_iff] at het; exact het.1 rfl
      have htn : t ≠ n := fun h => by rw [h] at htp; exact htp hpar
      have hmem : (⟨e, t, none⟩ : Move) ∈ legalMoves p := by
        have he : p.board e = some ⟨p.turn, .king⟩ := by rw [hb, ht, kbb_ok hae]
        have hpb := play_board_simple (m := ⟨e, t, none⟩) he (by simp) rfl (fun _ => het)
        simp only [legalMoves, List.mem_filter, Bool.not_eq_true']
        refine ⟨kingMove_mem_pseudoMoves he het ?_, ?_⟩
        · intro pc hpc
          rw [hb] at hpc
          simp [kbb, hta', hte, htn] at hpc
        · rw [hpb, ht]
          simp only
          have hbd : (fun x => if x = t then p.board e else if x = e then none else p.board x)
              = kbb c a t n := by
            funext x; simp only [hb, kbb]; split_ifs <;> simp_all
          rw [hbd]
          exact kbb_lone_safe (Ne.symm hta') hna (Ne.symm htn) hta (fun h => htp (h ▸ hpar))
      cases hl : legalMoves p with
      | nil => rw [hl] at hmem; simp at hmem
      | cons _ _ => simp [isCheckmate, hl]

/-- A legal move from a king-and-bishop position leads to a king-and-bishop position or (after
the capture of the bishop) to a bare-kings position. The bishop never captures the lone king:
by ray reversal the king would then already be in check. -/
theorem KBInv.play {p : Position} {m : Move} (h : KBInv p) (hm : m ∈ legalMoves p) :
    KKInv (Chess.play p m) ∨ KBInv (Chess.play p m) := by
  obtain ⟨c, a, e, n, hae, hna, hne, hb, hchk⟩ := h
  simp only [legalMoves, List.mem_filter, Bool.not_eq_true'] at hm
  obtain ⟨hps, hlg⟩ := hm
  have hkb : ∀ s pc, p.board s = some pc → pc.kind = .king ∨ pc.kind = .bishop :=
    fun s pc h => kbb_kind (hb ▸ h)
  obtain ⟨hpr, hmv, hdst⟩ := mem_pseudoMoves_KB hkb hps
  have hco := Color.other_ne c
  have hco' := Ne.symm hco
  have htn : (Chess.play p m).turn.other = p.turn := by rw [turn_play, Color.other_other]
  rcases Color.eq_or_eq_other p.turn c with ht | ht
  · have hlone : inCheck (kbb c a e n) c.other = false := by rw [← hb, ← ht]; exact hchk
    have hka := kingAdj_of_lone_safe hae hlone
    rcases hmv with ⟨hs, had⟩ | ⟨hs, d, hd, hray⟩
    · -- the strong king moves
      have hpb := play_board_simple hs (by simp) hpr (fun _ => had)
      rw [hb, ht, kbb_ck] at hs
      have hda : m.dst ≠ a := fun h => by
        rw [hs, h, kingAdj_iff] at had; exact had.1 rfl
      have hde : m.dst ≠ e := fun h => by
        rw [hs, h, kingAdj_comm, hka] at had; exact Bool.false_ne_true had
      have hdn : m.dst ≠ n := fun h => by
        refine hdst ⟨c, .bishop⟩ ?_ ht.symm
        rw [hb, h, kbb_cb hna hne]
      have hbd : (fun t => if t = m.dst then p.board m.src else if t = m.src then none else
          p.board t) = kbb c m.dst e n := by
        funext x; simp only [hb, kbb]; split_ifs <;> simp_all
      refine Or.inr ⟨c, m.dst, e, n, hde, Ne.symm hdn, hne, hpb.trans hbd, ?_⟩
      rw [htn, hpb, hbd]
      rw [hpb, hbd] at hlg
      exact hlg
    · -- the bishop moves
      have hpb := play_board_simple hs (by simp) hpr (by simp)
      have hs0 := hs
      rw [hb, ht, kbb_cb hna hne] at hs
      have hda : m.dst ≠ a := fun h => by
        refine hdst ⟨c, .king⟩ ?_ ht.symm
        rw [hb, h, kbb_ck]
      have hde : m.dst ≠ e := fun h => by
        rw [h] at hray
        have hbe : p.board e ≠ none := by rw [hb, kbb_ok hae |>.2 rfl]; simp
        have hrev := firstOnRay_of_mem_rayTargets hs0 hray hbe
        rw [hb, ht] at hrev
        rw [(inCheck_kbb_lone hae).2 (Or.inr ⟨_, neg_mem_bishopDirs hd, hrev⟩)] at hlone
        exact Bool.noConfusion hlone
      have hbd : (fun t => if t = m.dst then p.board m.src else if t = m.src then none else
          p.board t) = kbb c a e m.dst := by
        funext x; simp only [hb, kbb]; split_ifs <;> simp_all
      refine Or.inr ⟨c, a, e, m.dst, hae, hda, hde, hpb.trans hbd, ?_⟩
      rw [htn, hpb, hbd]
      rw [hpb, hbd] at hlg
      exact hlg
  · rw [hb, ht, Color.other_other, inCheck_kbb_strong hae] at hchk
    rcases hmv with ⟨hs, had⟩ | ⟨hs, -⟩
    · -- the lone king moves
      have hpb := play_board_simple hs (by simp) hpr (fun _ => had)
      rw [hb, ht, kbb_ok hae] at hs
      have hde : m.dst ≠ e := fun h => by
        rw [hs, h, kingAdj_iff] at had; exact had.1 rfl
      have hda : m.dst ≠ a := fun h => by
        rw [hs, h, kingAdj_comm, hchk] at had; exact Bool.false_ne_true had
      by_cases hdn : m.dst = n
      · have hbd : (fun t => if t = m.dst then p.board m.src else if t = m.src then none else
            p.board t) = kk2 c a m.dst := by
          funext x; simp only [hb, kbb, kk2]; split_ifs <;> simp_all
        refine Or.inl (KKInv.of_kk2 (Ne.symm hda) (hpb.trans hbd) ?_)
        rw [hpb]
        rw [hpb, ht] at hlg
        exact hlg
      · have hbd : (fun t => if t = m.dst then p.board m.src else if t = m.src then none else
            p.board t) = kbb c a m.dst n := by
          funext x; simp only [hb, kbb]; split_ifs <;> simp_all
        refine Or.inr ⟨c, a, m.dst, n, Ne.symm hda, hna, Ne.symm hdn, hpb.trans hbd, ?_⟩
        rw [htn, ht]
        rw [ht] at hlg
        exact hlg
    · rw [hb, ht] at hs
      exact absurd hs (kbb_ob _)

/-- The dead-position invariant for king and bishop: bare kings, or king and bishop against
king. -/
def DBInv (p : Position) : Prop := KKInv p ∨ KBInv p

/-- A position satisfying `DBInv` is dead. -/
theorem DBInv.isDead {p : Position} (h : DBInv p) : IsDead p := by
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

/-- A well-formed position with two kings and exactly one bishop (of colour `c`) satisfies the
king-and-bishop invariant. -/
theorem KBInv.of_wellFormed {p : Position} (hw : wellFormed p = true) (c : Color)
    (hm : kingsAnd ⟨c, .bishop⟩ p.board = true) (hn : countPiece p.board ⟨c, .bishop⟩ = 1) :
    KBInv p := by
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
  have hb : p.board = kbb c a e n := by
    funext s
    unfold kbb
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

/-- **King and bishop against king is dead** (FIDE 5.2.2, note `N-07`): a well-formed position
whose pieces are the two kings and exactly one bishop (of either colour `c`) is dead. Castling
flags, the en passant field and the halfmove clock are arbitrary. -/
theorem dead_KBK (p : Position) (c : Color) (hw : wellFormed p = true)
    (hm : kingsAnd ⟨c, .bishop⟩ p.board = true) (hn : countPiece p.board ⟨c, .bishop⟩ = 1) :
    IsDead p :=
  DBInv.isDead (Or.inr (KBInv.of_wellFormed hw c hm hn))

/-! ### Fixtures -/

/-- White: king e1, bishop c1; Black: king e8; Black to move. -/
def kbkPos : Position :=
  Position.ofList [(sq 4 1, ⟨.white, .king⟩), (sq 2 1, ⟨.white, .bishop⟩),
    (sq 4 8, ⟨.black, .king⟩)] .black

/-- `KB` vs `K` is dead (concrete instance of `dead_KBK`, dark-squared white bishop). -/
theorem kbkPos_dead : IsDead kbkPos := dead_KBK _ .white (by kernel_fact) (by kernel_fact)
  (by kernel_fact)

/-- Black: king a8, bishop f8; White: king a6; White to move. The lone king is white and the
black bishop is dark-squared. -/
def kbkPosBlack : Position :=
  Position.ofList [(sq 0 8, ⟨.black, .king⟩), (sq 5 8, ⟨.black, .bishop⟩),
    (sq 0 6, ⟨.white, .king⟩)] .white

/-- `K` vs `KB` with the bishop on the black side is dead. -/
theorem kbkPosBlack_dead : IsDead kbkPosBlack :=
  dead_KBK _ .black (by kernel_fact) (by kernel_fact) (by kernel_fact)

/-- White: king e1, bishop f1 (light-squared) giving check on h3; Black: king h3; Black to
move, in check. -/
def kbkPosCheck : Position :=
  Position.ofList [(sq 4 1, ⟨.white, .king⟩), (sq 5 1, ⟨.white, .bishop⟩),
    (sq 7 3, ⟨.black, .king⟩)] .black

/-- A `KBK` position in which the lone king is in check is still dead. -/
theorem kbkPosCheck_dead : IsDead kbkPosCheck :=
  dead_KBK _ .white (by kernel_fact) (by kernel_fact) (by kernel_fact)

/-- The lone king of `kbkPosCheck` is indeed in check (the fixture exercises the flight-square
argument). -/
theorem kbkPosCheck_inCheck : inCheck kbkPosCheck.board .black = true := by kernel_fact

/-- White: king e1, bishops c1 and f1; Black: king e8; Black to move. -/
def kbbkPos : Position :=
  Position.ofList [(sq 4 1, ⟨.white, .king⟩), (sq 2 1, ⟨.white, .bishop⟩),
    (sq 5 1, ⟨.white, .bishop⟩), (sq 4 8, ⟨.black, .king⟩)] .black

/-- Rejected fixture: with two bishops the count hypothesis of `dead_KBK` fails. -/
theorem kbbkPos_two_bishops : countPiece kbbkPos.board ⟨.white, .bishop⟩ = 2 := by kernel_fact

/-- Rejected fixture: the queen of `kqkFixture` is not a bishop, so `dead_KBK` does not apply. -/
theorem kqkFixture_not_kingsAndBishop : kingsAnd ⟨.white, .bishop⟩ kqkFixture.board = false := by
  kernel_fact

end LeanTheory.Chess
