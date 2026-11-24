"""Generate docs/chess-scenes.js: the positions shown on the website and slides, each with the
Lean declarations (docstring and statement, copied verbatim from the sources) that it illustrates.

Run from the repository root: python3 scripts/gen_chess_scenes.py
"""
import json
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = {p.relative_to(ROOT).as_posix(): p.read_text()
       for p in (ROOT / "LeanTheory").rglob("*.lean") if "KQKChunks" not in p.parts}


def decl(name, body=False):
    """Docstring and statement of the declaration `name` (up to `:=`, or the whole declaration
    if `body`), and the file it is in."""
    for path, text in SRC.items():
        m = re.search(r"(/--(?:(?!-/).)*?-/\n)?((?:@\[[^\]]*\]\s*)?(?:theorem|def|inductive|structure) "
                      + re.escape(name) + r"\b)", text, re.S)
        if not m:
            continue
        start = m.start(1) if m.group(1) else m.start(2)
        rest = text[m.start(2):]
        if body:
            end = re.search(r"\n\n", rest)
            stmt = rest[: end.start()] if end else rest
        else:
            end = re.search(r":=", rest)
            stmt = rest[: end.start()].rstrip()
        return {"code": (text[start:m.start(2)] + stmt).rstrip(), "file": path}
    raise KeyError(name)


def code(kind, head, name, body=False):
    d = decl(name, body)
    return {"kind": kind, "head": head, "code": d["code"], "file": d["file"]}


START = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR"
SCENES = [
    {"id": "kqk", "group": "Endgames", "title": "King and queen against king",
     "desc": "White plays the move of the table that the Lean kernel checked, entry by entry; "
             "Black plays the longest defence. Click the black king to play Black yourself, or "
             "pick a random position. The depth shown is the certified bound.",
     "board": {"mode": "kqk", "kqk": {"wk": "a1", "wq": "b2", "bk": "f5"}},
     "code": [code("goal", "Theorem", "kqk_forcesMate_wellFormed"),
              code("def", "The check of one table entry", "stateOK", True),
              code("ok", "Soundness of the check", "table_sound")]},
    {"id": "kqkBlack", "group": "KQK, Black to move", "title": "White still mates",
     "desc": "With Black to move there are four cases. Here every reply of Black leads to a "
             "certified mate; White plays the table, Black the longest defence.",
     "board": {"mode": "kqk", "kqk": {"wk": "e1", "wq": "a1", "bk": "e8", "turn": "b"}},
     "code": [code("goal", "Theorem", "kqk_black_to_move")]},
    {"id": "kqkBlackMated", "group": "KQK, Black to move", "title": "Black is mated",
     "desc": "Black to move, in check, no legal move.",
     "board": {"fen": "7k/6Q1/6K1/8/8/8/8/8", "turn": "b", "moves": [],
               "captions": ["kqkBlackMated: checkmate."]},
     "code": [code("sanity", "Sanity", "kqkBlackMated_checkmate")]},
    {"id": "kqkBlackStale", "group": "KQK, Black to move", "title": "Black is stalemated",
     "desc": "Black to move, not in check, no legal move: a draw.",
     "board": {"fen": "k7/2Q5/1K6/8/8/8/8/8", "turn": "b", "moves": [],
               "captions": ["kqkBlackStalemate: stalemate."]},
     "code": [code("sanity", "Sanity", "kqkBlackStalemate_stalemate")]},
    {"id": "kqkBlackCapture", "group": "KQK, Black to move", "title": "Black takes the queen",
     "desc": "The undefended queen can be captured; the bare kings are a dead position.",
     "board": {"fen": "4k3/4Q3/8/8/8/8/8/4K3", "turn": "b", "moves": ["e8e7"],
               "captions": ["Black to move.", "Kxe7: K v K, dead."]},
     "code": [code("sanity", "Sanity", "kqkBlackCapture_dead")]},
    {"id": "krk", "group": "King and rook", "title": "King and rook against king",
     "desc": "The rook version of the pipeline: White plays the move of the KRK table, which the "
             "Lean kernel is checking chunk by chunk; the longest defence needs 16 moves. Click "
             "the black king to play Black.",
     "board": {"mode": "krk", "krk": {"wk": "a1", "wq": "b2", "bk": "c3"}},
     "code": [code("ok", "Soundness of the check (compiled)", "krk_table_sound"),
              code("ok", "Bridge (compiled, conditional on the table)", "krk_forcesMate_of_table_wellFormed")]},
    {"id": "krkGame", "group": "King and rook", "title": "KRK: Black to move and the full game",
     "desc": "As for KQK: with Black to move, mate, stalemate, a capture of an undefended rook, or "
             "a forced mate; and from a fresh start with clock at most 118, White wins the game. "
             "Both are compiled for every table passing the check.",
     "board": {"fen": "8/8/8/8/8/8/3kR3/7K", "turn": "b", "moves": ["d2e2"],
               "captions": ["Black to move: the rook on e2 is undefended.", "Kxe2: K v K, dead."]},
     "code": [code("ok", "Black to move (compiled, conditional)", "krk_black_to_move_of_table"),
              code("ok", "Full game (compiled, conditional)", "krk_game_whiteWins_of_table_wellFormed")]},
    {"id": "kqkGame", "group": "Endgames", "title": "KQK in the full game",
     "desc": "The same result in the game with every automatic draw rule: from the start of a "
             "game in a KQK position, White forces a win and the game value is whiteWins.",
     "board": {"mode": "kqk", "kqk": {"wk": "e1", "wq": "d1", "bk": "e8"}},
     "code": [code("goal", "Theorem", "kqk_game_whiteWins_wellFormed")]},
    {"id": "initial", "group": "Rules", "title": "The initial position",
     "desc": "The rules are computable definitions. Counting legal move sequences from the "
             "initial position by kernel evaluation gives the standard values.",
     "board": {"fen": START, "moves": [], "captions": ["20 legal moves; 400 two-move sequences; 8,902 three-move sequences."]},
     "code": [code("def", "Legal moves", "legalMoves", True),
              code("sanity", "Sanity", "perft_three")]},
    {"id": "fools", "group": "Rules", "title": "Fool's mate",
     "desc": "Every move is checked to be legal, and the final position is checkmate.",
     "board": {"fen": START, "moves": ["f2f3", "e7e5", "g2g4", "d8h4"],
               "captions": ["Start.", "1. f3", "1... e5", "2. g4", "2... Qh4#: White is checkmated."]},
     "code": [code("sanity", "Sanity", "foolsMate_checkmate")]},
    {"id": "castle", "group": "Rules", "title": "Castling",
     "desc": "Castling is the king's two-square move; the rook follows. It is illegal through an "
             "attacked square and after the king has moved, even if it returns.",
     "board": {"fen": "k7/8/8/8/8/8/8/4K2R", "moves": ["e1g1"],
               "captions": ["White has the kingside castling right.", "O-O: the rook lands on f1."]},
     "code": [code("sanity", "Sanity", "castle_legal"), code("sanity", "Sanity", "castle_through_check"),
              code("sanity", "Sanity", "castle_after_king_moved")]},
    {"id": "ep", "group": "Rules", "title": "En passant",
     "desc": "Legal only immediately after the double step, and it removes the captured pawn.",
     "board": {"fen": "k7/3p4/8/4P3/8/8/8/7K", "turn": "b", "moves": ["d7d5", "e5d6"],
               "captions": ["Black to move.", "1... d5: a double step past e5.", "2. exd6 e.p.: the pawn on d5 disappears."]},
     "code": [code("sanity", "Sanity", "enPassant_legal"), code("sanity", "Sanity", "enPassant_expires")]},
    {"id": "promo", "group": "Rules", "title": "Promotion",
     "desc": "A pawn reaching the last rank must become a queen, rook, bishop or knight: exactly "
             "four legal moves to b8.",
     "board": {"fen": "7k/1P6/8/8/8/8/8/7K", "moves": ["b7b8q"],
               "captions": ["White to move.", "b8=Q (b8=R, b8=B, b8=N are the other three)."]},
     "code": [code("sanity", "Sanity", "promotion_four")]},
    {"id": "double", "group": "Rules", "title": "Double check",
     "desc": "After the discovered double check Ne4-f6+, only king moves are legal.",
     "board": {"fen": "4k3/8/q7/8/4N3/8/7K/r3R3", "moves": ["e4f6"],
               "captions": ["White to move.", "Nf6+: knight and rook both give check; Black has exactly Kd8, Kf8, Kf7."]},
     "code": [code("sanity", "Sanity", "doubleCheck_only_king")]},
    {"id": "kiwipete", "group": "Rules", "title": "Kiwipete",
     "desc": "A standard test position full of special moves: 48 legal moves and 2,039 two-move "
             "sequences, as computed by the kernel.",
     "board": {"fen": "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R", "moves": [],
               "captions": ["perft 1 = 48, perft 2 = 2,039 (chessprogramming.org, Position 2)."]},
     "code": [code("sanity", "Sanity", "kiwipete_perft_two")]},
    {"id": "mate1", "group": "Draws and mates", "title": "Mate in one",
     "desc": "The forced-mate checker finds Qg7#, and its soundness theorem turns the computation "
             "into the inductive predicate ForcesMate.",
     "board": {"fen": "7k/Q7/6K1/8/8/8/8/8", "moves": ["a7g7"],
               "captions": ["White to move.", "Qg7#."]},
     "code": [code("def", "Forced mate", "ForcesMate", True), code("sanity", "Sanity", "mateInOne")]},
    {"id": "stalemate", "group": "Draws and mates", "title": "The stalemate trap",
     "desc": "From the same position, Qf7 takes every square from the black king without check: "
             "stalemate, a draw. This is the hazard the user idea 'guard against stalemates' names.",
     "board": {"fen": "7k/Q7/6K1/8/8/8/8/8", "moves": ["a7f7"],
               "captions": ["White to move.", "Qf7?? stalemate."]},
     "code": [code("sanity", "Sanity", "stalemateTrap")]},
    {"id": "fivefold", "group": "Draws and mates", "title": "Fivefold repetition",
     "desc": "Knights out and back four times: the initial position appears for the fifth time and "
             "the game is drawn automatically (FIDE 9.6.1).",
     "board": {"fen": START, "moves": ["g1f3", "g8f6", "f3g1", "f6g8"] * 4, "speed": 500,
               "captions": ["Occurrence 1."] + [""] * 3 + ["Occurrence 2."] + [""] * 3 + ["Occurrence 3."]
               + [""] * 3 + ["Occurrence 4."] + [""] * 3 + ["Occurrence 5: drawn."]},
     "code": [code("sanity", "Sanity", "fivefold_draw")]},
    {"id": "deadKK", "group": "Dead positions", "title": "King against king",
     "desc": "No sequence of legal moves leads to checkmate: proved for every well-formed position "
             "with only the two kings, by an invariant closed under legal moves.",
     "board": {"fen": "4k3/8/8/8/8/8/8/4K3", "moves": []},
     "code": [code("goal", "Theorem", "dead_KK")]},
    {"id": "deadKNK", "group": "Dead positions", "title": "King and knight against king",
     "desc": "A king checked by a lone knight always has a flight square: a neighbour of the other "
             "colour that the enemy king cannot cover.",
     "board": {"fen": "4k3/8/8/8/8/8/8/1N2K3", "turn": "b", "moves": []},
     "code": [code("goal", "Theorem", "dead_KNK")]},
    {"id": "deadKBK", "group": "Dead positions", "title": "King and bishop against king",
     "desc": "A bishop only attacks squares of its own colour, and it can never capture the lone "
             "king: here the black king is in check and still the position is dead.",
     "board": {"fen": "8/8/8/8/8/7k/8/4KB2", "turn": "b", "moves": []},
     "code": [code("goal", "Theorem", "dead_KBK")]},
    {"id": "determined", "group": "Perfect play", "title": "Chess is determined",
     "desc": "Under the FIDE automatic draw rules, chess is a finite game, so from the initial "
             "position exactly one of three outcomes can be forced. Which one is not known.",
     "board": {"fen": START, "moves": []},
     "code": [code("goal", "Theorem", "chess_determined_initial")]},
]

# Further declarations shown on the slides, by name: (name, whole declaration?).
DECLS = [("Position", True), ("legalMoves", True), ("samePosition", True),
         ("GameState.automaticDraw", True), ("IsDead", True), ("ForcesMate", True),
         ("forcesMateB_sound", False), ("Game.exactly_one_outcome", False),
         ("chess_determined_initial", False), ("chessGame", True), ("history_length_le", False),
         ("stateOK", True), ("afterWhiteOK", True), ("table_sound", False),
         ("play_kqk_black", False), ("kqk_forcesMate_wellFormed", False),
         ("kqk_game_whiteWins_wellFormed", False), ("KQKNode.rank_eq_of_same", False),
         ("kqk_black_to_move", False), ("dead_KK", False), ("dead_KNK", False), ("dead_KBK", False),
         ("knk_flight", False), ("initial_not_dead", False), ("kqk_row_0_9", False),
         ("krkStateOK", True), ("krk_table_sound", False), ("krk_forcesMate_of_table_wellFormed", False),
         ("krk_black_to_move_of_table", False), ("krk_game_whiteWins_of_table_wellFormed", False),
         ("play_krk_rook", False), ("dead_KBK", False)]
CHUNK = (ROOT / "LeanTheory/Certificates/Chess/KQKChunks/C00.lean").read_text()
SRC["LeanTheory/Certificates/Chess/KQKChunks/C00.lean"] = CHUNK


def decl_any(name, body):
    short = name.split(".")[-1]
    try:
        return decl(name, body)
    except KeyError:
        return decl(short, body)


DECL_OUT = {n: decl_any(n, b) for n, b in DECLS}

out = "/* Generated by scripts/gen_chess_scenes.py from the Lean sources. */\nwindow.CHESS_SCENES = " \
      + json.dumps(SCENES, ensure_ascii=False, indent=1) + ";\nwindow.CHESS_DECLS = " \
      + json.dumps(DECL_OUT, ensure_ascii=False, indent=1) + ";\n"
(ROOT / "docs/chess-scenes.js").write_text(out)
print(len(SCENES), "scenes;", len(out), "bytes")
