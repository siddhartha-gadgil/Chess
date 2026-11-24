/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import Mathlib.Data.Fintype.Basic

/-!
# Kernel: the rules of chess (board, positions, legal moves)

**This is a kernel file.** It encodes the Basic Rules of Play of the FIDE *Laws of Chess*
(in force from 2023-01-01, Articles 2 and 3; source `S-1` in `notes/implementation-plan.md`,
note `N-02`) as **computable definitions**. The rules of chess are a definition of a game, not an
empirical law, so there is no law typeclass here: the modelling risk is *fidelity* to the FIDE
text, which is tested by the sanity suite `LeanTheory.Sanity.Chess.Rules` (perft counts, castling,
en passant, promotion, pins, checkmate and stalemate fixtures).

Encoding:

* `Square := Fin 64`, with index `8 * rank + file`, files `a…h = 0…7`, ranks `1…8 = 0…7`
  (so `a1 = 0`, `h1 = 7`, `a8 = 56`). `sq f r` is the square on file `f` (`0…7`) and rank `r`
  (`1…8`, as written in chess notation).
* `Board := Square → Option Piece`.
* `Position`: board, side to move, castling rights, en passant target (the square passed over by
  a pawn double step on the previous move, as in FEN) and halfmove clock (moves since the last
  pawn move or capture, used by the 75-move rule of `N-03`).
* `Move`: source, destination and optional promotion piece. Castling is the king moving two
  squares; en passant is a pawn moving diagonally onto the en passant target.
* `pseudoMoves` (Articles 3.1–3.8, ignoring Article 3.9 except for the castling conditions of
  3.8.2.2), `play` (the effect of a move), `inCheck` (Article 3.9.1) and `legalMoves`
  (Article 3.9.2: pseudo-legal moves that do not leave one's own king in check).
* `isCheckmate`, `isStalemate` (Articles 1.4, 5.1.1, 5.2.1) and `perft`.

Scope and conventions:

* Positions are not required to be reachable (FIDE 3.10.3). Functions are total on all values of
  `Position`; on ill-formed positions (no king, several kings, pawns on the last rank) they
  return *some* answer with no claimed meaning. `inCheck` is `false` when the king is missing.
* Draw rules depending on history (repetition, 75-move rule) and dead positions are not here;
  they are part of `N-03`.
-/

@[expose] public section

namespace LeanTheory.Chess

/-- The two players. -/
inductive Color where
  /-- White, who moves first. -/
  | white
  /-- Black. -/
  | black
  deriving DecidableEq, Repr, Inhabited

/-- The opponent of a player. -/
def Color.other : Color → Color
  | .white => .black
  | .black => .white

/-- The six kinds of chess pieces (FIDE Article 2.2). -/
inductive PieceType where
  /-- Pawn. -/
  | pawn
  /-- Knight. -/
  | knight
  /-- Bishop. -/
  | bishop
  /-- Rook. -/
  | rook
  /-- Queen. -/
  | queen
  /-- King. -/
  | king
  deriving DecidableEq, Repr

/-- A piece: a colour and a kind. -/
structure Piece where
  /-- The player owning the piece. -/
  color : Color
  /-- The kind of piece. -/
  kind : PieceType
  deriving DecidableEq, Repr

/-- The 64 squares; index `8 * rank + file` with `a1 = 0`, `h1 = 7`, `a8 = 56`. -/
abbrev Square := Fin 64

/-- The file of a square, `0` (a-file) to `7` (h-file). -/
def Square.file (s : Square) : Nat := s.val % 8

/-- The rank of a square, `0` (first rank) to `7` (eighth rank). -/
def Square.rank (s : Square) : Nat := s.val / 8

/-- The square on file `f` (`0…7` for `a…h`) and rank `r` (`1…8`, chess notation). Arguments out
of range are reduced modulo 8. -/
def sq (f r : Nat) : Square := ⟨((r - 1) % 8) * 8 + f % 8, by omega⟩

/-- The square with index `n`, if `n < 64`. -/
def Square.ofNat? (n : Nat) : Option Square := if h : n < 64 then some ⟨n, h⟩ else none

/-- The square displaced by `df` files and `dr` ranks, if it lies on the board. (Coordinates are
offset by 8 so that the bounds checks are comparisons of natural numbers, which the Lean kernel
evaluates much faster than integer comparisons; displacements satisfy `|df|, |dr| ≤ 8` in all
uses, and larger negative ones give `none`.) -/
def Square.shift (s : Square) (df dr : Int) : Option Square :=
  let f : Nat := ((s.file + 8 : Nat) + df).toNat
  let r : Nat := ((s.rank + 8 : Nat) + dr).toNat
  if 8 ≤ f ∧ f < 16 ∧ 8 ≤ r ∧ r < 16 then Square.ofNat? ((r - 8) * 8 + (f - 8)) else none

/-- All 64 squares, in index order. -/
def allSquares : List Square := (List.range 64).filterMap Square.ofNat?

/-- A board assigns to each square at most one piece. -/
abbrev Board := Square → Option Piece

/-- The four castling rights (FIDE 3.8.2.1: lost for good once the king or that rook moves). -/
structure CastlingRights where
  /-- White may still castle kingside (with the h1 rook). -/
  whiteKing : Bool
  /-- White may still castle queenside (with the a1 rook). -/
  whiteQueen : Bool
  /-- Black may still castle kingside (with the h8 rook). -/
  blackKing : Bool
  /-- Black may still castle queenside (with the a8 rook). -/
  blackQueen : Bool
  deriving DecidableEq, Repr

/-- No castling rights. -/
def CastlingRights.none : CastlingRights := ⟨false, false, false, false⟩

/-- All castling rights. -/
def CastlingRights.all : CastlingRights := ⟨true, true, true, true⟩

/-- The kingside castling right of a player. -/
def CastlingRights.kingSide (cr : CastlingRights) : Color → Bool
  | .white => cr.whiteKing
  | .black => cr.blackKing

/-- The queenside castling right of a player. -/
def CastlingRights.queenSide (cr : CastlingRights) : Color → Bool
  | .white => cr.whiteQueen
  | .black => cr.blackQueen

/-- Castling rights after a move from `src` to `dst`: a move from or to a king's or rook's
initial square removes the corresponding rights (a king move, a rook move, or the capture of a
rook on its initial square). -/
def CastlingRights.update (cr : CastlingRights) (src dst : Square) : CastlingRights :=
  let touched (n : Nat) : Bool := src.val == n || dst.val == n
  { whiteKing := cr.whiteKing && !touched 4 && !touched 7
    whiteQueen := cr.whiteQueen && !touched 4 && !touched 0
    blackKing := cr.blackKing && !touched 60 && !touched 63
    blackQueen := cr.blackQueen && !touched 60 && !touched 56 }

/-- A chess position: everything the legality of the next move depends on, plus the halfmove
clock for the 75-move rule. -/
structure Position where
  /-- The placement of the pieces. -/
  board : Board
  /-- The player to move. -/
  turn : Color
  /-- The remaining castling rights. -/
  castling : CastlingRights
  /-- The square passed over by a pawn double step on the previous move, if any. -/
  epTarget : Option Square
  /-- The number of moves (plies) since the last capture or pawn move. -/
  halfmove : Nat

/-- A move: source square, destination square and, for a pawn reaching the last rank, the piece
it is exchanged for. Castling is encoded as the king's two-square move. -/
structure Move where
  /-- The square the moving piece leaves. -/
  src : Square
  /-- The square the moving piece arrives on. -/
  dst : Square
  /-- The promotion piece, if any. -/
  promo : Option PieceType
  deriving DecidableEq, Repr

/-- The move from `sq f₁ r₁` to `sq f₂ r₂` without promotion (files `0…7`, ranks `1…8`). -/
def mv (f₁ r₁ f₂ r₂ : Nat) : Move := ⟨sq f₁ r₁, sq f₂ r₂, none⟩

/-! ### Directions -/

/-- Knight displacements (FIDE 3.6). -/
def knightDeltas : List (Int × Int) :=
  [(1, 2), (2, 1), (2, -1), (1, -2), (-1, -2), (-2, -1), (-2, 1), (-1, 2)]

/-- King displacements (FIDE 3.8.1). -/
def kingDeltas : List (Int × Int) :=
  [(1, 0), (1, 1), (0, 1), (-1, 1), (-1, 0), (-1, -1), (0, -1), (1, -1)]

/-- Rook directions (FIDE 3.3). -/
def rookDirs : List (Int × Int) := [(1, 0), (-1, 0), (0, 1), (0, -1)]

/-- Bishop directions (FIDE 3.2). -/
def bishopDirs : List (Int × Int) := [(1, 1), (1, -1), (-1, 1), (-1, -1)]

/-- The direction in which a player's pawns advance: `+1` rank for White, `-1` for Black. -/
def Color.forward : Color → Int
  | .white => 1
  | .black => -1

/-- The rank (`0…7`) on which a player's pawns start. -/
def Color.pawnRank : Color → Nat
  | .white => 1
  | .black => 6

/-- The rank (`0…7`) on which a player's pawns promote. -/
def Color.lastRank : Color → Nat
  | .white => 7
  | .black => 0

/-- The home rank in chess notation (`1` or `8`), used for castling squares. -/
def Color.homeRank : Color → Nat
  | .white => 1
  | .black => 8

/-! ### Attacks and check -/

/-- The first piece met when moving from `s` in direction `(df, dr)`, looking at most `n` steps. -/
def firstOnRay (b : Board) (df dr : Int) : Nat → Square → Option Piece
  | 0, _ => none
  | n + 1, s =>
    match s.shift df dr with
    | none => none
    | some t =>
      match b t with
      | some p => some p
      | none => firstOnRay b df dr n t

/-- Is there a piece `p` on one of the squares `s + d`, `d ∈ ds`? -/
def pieceAtOffsets (b : Board) (p : Piece) (s : Square) (ds : List (Int × Int)) : Bool :=
  ds.any fun d =>
    match s.shift d.1 d.2 with
    | some t => b t == some p
    | none => false

/-- Is the square `s` attacked by a piece of colour `c` (FIDE 3.1.3: a piece attacks a square if
it could capture there)? Pawns attack diagonally forward; sliding pieces are blocked by the first
piece on the line. -/
def attackedBy (b : Board) (c : Color) (s : Square) : Bool :=
  pieceAtOffsets b ⟨c, .knight⟩ s knightDeltas ||
  pieceAtOffsets b ⟨c, .king⟩ s kingDeltas ||
  pieceAtOffsets b ⟨c, .pawn⟩ s [(-1, -c.forward), (1, -c.forward)] ||
  rookDirs.any (fun d =>
    match firstOnRay b d.1 d.2 7 s with
    | some p => p == ⟨c, .rook⟩ || p == ⟨c, .queen⟩
    | none => false) ||
  bishopDirs.any (fun d =>
    match firstOnRay b d.1 d.2 7 s with
    | some p => p == ⟨c, .bishop⟩ || p == ⟨c, .queen⟩
    | none => false)

/-- The square of the king of colour `c` (the first one in index order), if any. -/
def kingSquare (b : Board) (c : Color) : Option Square :=
  allSquares.find? fun s => b s == some ⟨c, .king⟩

/-- Is the king of colour `c` in check (FIDE 3.9.1)? `false` if there is no such king. -/
def inCheck (b : Board) (c : Color) : Bool :=
  match kingSquare b c with
  | some k => attackedBy b c.other k
  | none => false

/-! ### Pseudo-legal moves -/

/-- Destinations of a non-sliding piece of colour `c` on `s` with displacements `ds`: on the
board and not occupied by a piece of its own colour. -/
def stepTargets (b : Board) (c : Color) (s : Square) (ds : List (Int × Int)) : List Square :=
  ds.filterMap fun d =>
    match s.shift d.1 d.2 with
    | some t =>
      match b t with
      | some p => if p.color = c then none else some t
      | none => some t
    | none => none

/-- Destinations of a sliding piece of colour `c` from `s` in direction `(df, dr)`: empty squares
up to and including the first opponent piece, at most `n` steps. -/
def rayTargets (b : Board) (c : Color) (df dr : Int) : Nat → Square → List Square
  | 0, _ => []
  | n + 1, s =>
    match s.shift df dr with
    | none => []
    | some t =>
      match b t with
      | none => t :: rayTargets b c df dr n t
      | some p => if p.color = c then [] else [t]

/-- The four promotion choices (FIDE 3.7.3.3). -/
def promoKinds : List PieceType := [.queen, .rook, .bishop, .knight]

/-- Pawn moves from `s` to `t` for a pawn of colour `c`: four promotion moves if `t` is on the
last rank, otherwise the plain move. -/
def pawnMovesTo (c : Color) (s t : Square) : List Move :=
  if t.rank = c.lastRank then promoKinds.map fun k => ⟨s, t, some k⟩ else [⟨s, t, none⟩]

/-- Pseudo-legal pawn moves from `s` for the side to move (FIDE 3.7): single and initial double
advance onto empty squares, diagonal captures, en passant onto the en passant target, with
promotion on the last rank. -/
def pawnMoves (p : Position) (s : Square) : List Move :=
  let c := p.turn
  let b := p.board
  let advances : List Move :=
    match s.shift 0 c.forward with
    | some t =>
      if b t = none then
        pawnMovesTo c s t ++
          (if s.rank = c.pawnRank then
            match t.shift 0 c.forward with
            | some u => if b u = none then [⟨s, u, none⟩] else []
            | none => []
          else [])
      else []
    | none => []
  let captures : List Move :=
    [(-1 : Int), 1].flatMap fun df =>
      match s.shift df c.forward with
      | some t =>
        match b t with
        | some q => if q.color = c then [] else pawnMovesTo c s t
        | none => if p.epTarget = some t then [⟨s, t, none⟩] else []
      | none => []
  advances ++ captures

/-- Castling moves for the side to move (FIDE 3.8.2): the right is still held, king and rook
stand on their initial squares, the squares between them are empty, and the king's square, the
square it crosses and its destination are not attacked. -/
def castlingMoves (p : Position) : List Move :=
  let c := p.turn
  let b := p.board
  let o := c.other
  let r := c.homeRank
  let kingHome := b (sq 4 r) == some ⟨c, .king⟩
  let kingSide : List Move :=
    if p.castling.kingSide c && kingHome && b (sq 7 r) == some ⟨c, .rook⟩ &&
        b (sq 5 r) == none && b (sq 6 r) == none &&
        !attackedBy b o (sq 4 r) && !attackedBy b o (sq 5 r) && !attackedBy b o (sq 6 r) then
      [⟨sq 4 r, sq 6 r, none⟩]
    else []
  let queenSide : List Move :=
    if p.castling.queenSide c && kingHome && b (sq 0 r) == some ⟨c, .rook⟩ &&
        b (sq 1 r) == none && b (sq 2 r) == none && b (sq 3 r) == none &&
        !attackedBy b o (sq 4 r) && !attackedBy b o (sq 3 r) && !attackedBy b o (sq 2 r) then
      [⟨sq 4 r, sq 2 r, none⟩]
    else []
  kingSide ++ queenSide

/-- Pseudo-legal moves of the piece of kind `k` on `s` belonging to the side to move. -/
def pieceMoves (p : Position) (s : Square) (k : PieceType) : List Move :=
  let plain (ts : List Square) : List Move := ts.map fun t => ⟨s, t, none⟩
  let slide (ds : List (Int × Int)) : List Move :=
    plain (ds.flatMap fun d => rayTargets p.board p.turn d.1 d.2 7 s)
  match k with
  | .pawn => pawnMoves p s
  | .knight => plain (stepTargets p.board p.turn s knightDeltas)
  | .bishop => slide bishopDirs
  | .rook => slide rookDirs
  | .queen => slide (rookDirs ++ bishopDirs)
  | .king => plain (stepTargets p.board p.turn s kingDeltas)

/-- All pseudo-legal moves of the side to move: moves obeying FIDE 3.1–3.8 that may leave the
mover's own king in check. -/
def pseudoMoves (p : Position) : List Move :=
  allSquares.flatMap (fun s =>
    match p.board s with
    | some pc => if pc.color = p.turn then pieceMoves p s pc.kind else []
    | none => []) ++
  castlingMoves p

/-! ### Making a move -/

/-- The position after making the move `m` (assumed pseudo-legal): moves the piece (exchanging a
promoted pawn), removes a pawn captured en passant, moves the rook when castling, updates castling
rights, the en passant target and the halfmove clock, and passes the move to the opponent. -/
def play (p : Position) (m : Move) : Position :=
  let b := p.board
  let c := p.turn
  let mover := b m.src
  let isPawn := mover == some ⟨c, .pawn⟩
  let isKing := mover == some ⟨c, .king⟩
  let isCapture := (b m.dst).isSome
  let isEp := isPawn && p.epTarget == some m.dst && (b m.dst).isNone &&
    m.src.file != m.dst.file
  let placed : Option Piece :=
    match m.promo with
    | some k => some ⟨c, k⟩
    | none => mover
  let b₁ : Board := fun t => if t = m.dst then placed else if t = m.src then none else b t
  let b₂ : Board :=
    if isEp then
      match m.dst.shift 0 (-c.forward) with
      | some v => fun t => if t = v then none else b₁ t
      | none => b₁
    else b₁
  let rookMove : Option (Square × Square) :=
    if isKing && m.dst.val == m.src.val + 2 then
      match Square.ofNat? (m.src.val + 3), Square.ofNat? (m.src.val + 1) with
      | some rf, some rt => some (rf, rt)
      | _, _ => none
    else if isKing && m.src.val == m.dst.val + 2 then
      match Square.ofNat? (m.src.val - 4), Square.ofNat? (m.src.val - 1) with
      | some rf, some rt => some (rf, rt)
      | _, _ => none
    else none
  let b₃ : Board :=
    match rookMove with
    | some (rf, rt) => fun t => if t = rt then b rf else if t = rf then none else b₂ t
    | none => b₂
  let ep : Option Square :=
    if isPawn && (m.dst.val == m.src.val + 16 || m.src.val == m.dst.val + 16) then
      m.src.shift 0 c.forward
    else none
  { board := b₃
    turn := c.other
    castling := p.castling.update m.src m.dst
    epTarget := ep
    halfmove := if isPawn || isCapture then 0 else p.halfmove + 1 }

/-! ### Legal moves and terminal positions -/

/-- The legal moves (FIDE 3.10.1): pseudo-legal moves after which the mover's king is not in check
(FIDE 3.9.2). -/
def legalMoves (p : Position) : List Move :=
  (pseudoMoves p).filter fun m => !inCheck (play p m).board p.turn

/-- Is `m` a legal move in `p`? -/
def isLegal (p : Position) (m : Move) : Bool := (legalMoves p).contains m

/-- Checkmate (FIDE 1.4, 5.1.1): the side to move is in check and has no legal move. -/
def isCheckmate (p : Position) : Bool := inCheck p.board p.turn && (legalMoves p).isEmpty

/-- Stalemate (FIDE 5.2.1): the side to move is not in check and has no legal move. -/
def isStalemate (p : Position) : Bool := !inCheck p.board p.turn && (legalMoves p).isEmpty

/-- Play a sequence of moves, failing (`none`) as soon as one of them is not legal. -/
def playLegal : Position → List Move → Option Position
  | p, [] => some p
  | p, m :: ms => if isLegal p m then playLegal (play p m) ms else none

/-- The number of legal move sequences of length `n` from `p` (performance test, "perft"). -/
def perft : Nat → Position → Nat
  | 0, _ => 1
  | n + 1, p => ((legalMoves p).map fun m => perft n (play p m)).sum

/-! ### The initial position and position builders -/

/-- The piece kinds on the first and eighth ranks, by file (FIDE 2.3). -/
def backRankKind (f : Nat) : PieceType :=
  match f with
  | 0 => .rook
  | 1 => .knight
  | 2 => .bishop
  | 3 => .queen
  | 4 => .king
  | 5 => .bishop
  | 6 => .knight
  | _ => .rook

/-- The initial placement of the pieces (FIDE 2.3). -/
def initialBoard : Board := fun s =>
  match s.rank with
  | 0 => some ⟨.white, backRankKind s.file⟩
  | 1 => some ⟨.white, .pawn⟩
  | 6 => some ⟨.black, .pawn⟩
  | 7 => some ⟨.black, backRankKind s.file⟩
  | _ => none

/-- The initial position: White to move, all castling rights, no en passant target. -/
def initialPosition : Position :=
  ⟨initialBoard, .white, .all, none, 0⟩

/-- The board with the listed pieces and all other squares empty (the first entry wins on a
repeated square). -/
def Board.ofList (l : List (Square × Piece)) : Board := fun s =>
  (l.find? fun e => e.1 == s).map Prod.snd

/-- A position from a list of pieces and the side to move, with no castling rights, no en passant
target and halfmove clock `0`. -/
def Position.ofList (l : List (Square × Piece)) (turn : Color) : Position :=
  ⟨Board.ofList l, turn, .none, none, 0⟩

end LeanTheory.Chess
