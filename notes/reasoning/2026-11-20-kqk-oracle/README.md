# 2026-11-20-kqk-oracle — KQK retrograde analysis (untrusted oracle)

| Field | Value |
| --- | --- |
| Input | `N-06` (computation for `N-05`, `Q-4`, `Q-8`, `G-2`) |
| Mode | exploratory computation |
| Status | done |
| Evidence state | **numerical observation (untrusted Python)**: not a proof, not evidence for `G-2` until checked in Lean |
| Outcome | Every White-to-move KQK state is a forced win; max DTM = 10 (confirms the cited figure); certificate format proposed for `N-05` (b) |

## Model

Three pieces only: white king `wk`, white queen `wq`, black king `bk`; no castling, no pawns,
no en passant. Kings move one square, the queen slides and is blocked by pieces, a move may not
leave one's own king attacked, kings may never be adjacent. Black may capture the queen if it is
not adjacent to the white king; the result K vs K is dead (draw), so such a Black-to-move state is
classed `C` (draw, Black need not capture but can). Checkmate: in check with no legal move;
stalemate: not in check with no legal move (draw).

States `(wk, wq, bk, side)` with squares as in `LeanTheory/Kernel/Chess/Rules.lean`
(`Square = Fin 64`, index `8*rank + file`, `a1 = 0`, `h1 = 7`, `a8 = 56`). *Well formed*: three
distinct squares, kings not adjacent, side not to move not in check (with White to move Black is
not in check; the white king can only be attacked by adjacency, already excluded).

DTM = number of White moves to mate with optimal play by both sides.

## Results (numerical observations)

| Quantity | All states | Up to 8-fold symmetry (orbits) |
| --- | --- | --- |
| White-to-move (WTM) states | 144 508 | 18 081 |
| Black-to-move (BTM) states | 223 944 | 28 056 |
| Total | 368 452 | 46 137 |

**WTM:** all 144 508 are forced wins. **Maximum DTM = 10**, attained by exactly 8 states, one
orbit: `wk a1, wq b2, bk f5` (White to move). DTM distribution:

| DTM | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| WTM states | 2448 | 5012 | 9064 | 19964 | 26164 | 32064 | 32104 | 15000 | 2680 | 8 |
| WTM orbits | 306 | 629 | 1135 | 2499 | 3273 | 4010 | 4016 | 1877 | 335 | 1 |

**BTM** classes:

| Class | States | Orbits |
| --- | --- | --- |
| White mates in n (Black has moves, none captures) | 200 532 | 25 114 |
| `C` Black can capture the undefended queen (draw) | 22 176 | 2 787 |
| `S` stalemate | 872 | 109 |
| `M0` already checkmated | 364 | 46 |

BTM mate-in-n distribution (states / orbits): 1: 1352/169, 2: 2956/372, 3: 7480/936,
4: 14144/1773, 5: 25484/3190, 6: 39908/4997, 7: 54052/6769, 8: 43800/5483, 9: 11300/1417,
10: 56/8. Max 10.

Principal variation from the DTM-10 state (Black's longest-resisting replies):
`1.Kb1 Ke6 2.Kc2 Kf5 3.Kd3 Ke6 4.Ke4 Kd6 5.Qc2 Ke6 6.Qc6+ Kf7 7.Kf5 Kg7 8.Qd7+ Kh8 9.Kg6 Kg8
10.Qg7#` (one optimal line; others exist).

### Draw rules other than capture/stalemate

- Max DTM 10 means at most 19 plies (WTM) or 20 plies (BTM, mate in 10) to mate, far below the
  150 plies of the 75-move rule (FIDE 9.6.2). **But** the `Position` structure carries a halfmove
  clock: a state with clock `h` near 150 could be drawn before mate. The `N-05` theorem needs a
  hypothesis such as `h + 19 ≤ 150` for WTM (`h + 20 ≤ 150` for BTM), or must quantify over
  `h = 0`; the exact boundary depends on how `N-03` encodes "checkmate on the last move takes
  precedence". No capture or pawn move happens on the winning line, so the clock only grows.
- Fivefold repetition (9.6.1): along the certified line the WTM DTM strictly decreases, so no
  position repeats *within* the line. If the state carries repetition history, a position already
  seen four times could still trigger it; `N-05` should assume an empty (or harmless) history.

## Cross-checks

- `kqk_validate.py` is an independent re-implementation (0x88 mailbox, generic legality by "make
  the move, is the mover's king attacked by any enemy piece, including the enemy king") that does
  not reuse the oracle's shortcuts. It checks, with **0 errors**:
  V1 the well-formed state sets coincide; V2 every BTM value satisfies its defining equation
  (`M0`, `S`, `C`, or `max` of reply DTMs); V3 for every WTM state of DTM `d`, the stored move is
  legal and either mates (then `d = 1`) or every Black reply is a non-capture to DTM `≤ d−1`;
  V4 no White move reaches a BTM value `< d−1` (or mate when `d > 1`), so depths are exact;
  V5 no WTM state is undecided. V3+V5 alone imply the stored strategy mates within `d`.
- Oracle-internal: DTM and BTM values are invariant under all 8 symmetries (asserted).
- **Sourced:** Wikipedia, "Checkmate", section *King and queen* (fetched 2026-11-20): "checkmate
  can be forced in at most ten moves from any starting position"; at most nine after a pawn has
  just promoted. Agrees with max DTM 10.
- **Recalled, not sourced:** the figure 28 056 is, as I recall it, sometimes quoted as the number
  of KQK positions up to symmetry; here it equals the BTM orbit count, which suggests that quote
  counts Black-to-move (or "legal, either side") positions under a convention I could not pin
  down. The order-of-magnitude range "28 000–40 000" in `N-05`/`S-6` is consistent with 18 081
  WTM + 28 056 BTM orbits. Treat as unverified.

## Certificate proposal for `N-05` route (b)

**Data.** For each canonical WTM state (18 081 rows): `(wk, wq, bk, d, src, dst)`, i.e. the move
and its depth, `d ∈ 1..10` (`computations/kqk_wtm_canonical_cert.tsv`). Canonical form:
lexicographically least `(wk, wq, bk)` over the 8 symmetries; the canonical white king lies in
the triangle a1–d1–d4 (10 squares). Packed, a row is 18 bits key + 4 bits depth + 12 bits move
≈ 34 bits, ~77 KB; or a dense depth table indexed by `wk*4096 + wq*64 + bk` (4 bits × 2¹⁸
= 128 KB) with the move stored only for canonical rows. No depths are needed for BTM states.

**Check (Boolean, by kernel evaluation, e.g. `bool_cert`).** For each row with depth `d`:
1. `(src, dst)` is in `legalMoves` of the KQK position; let `t` be the result;
2. if `legalMoves t = []` then `inCheck t` and `d = 1`;
3. otherwise every Black reply keeps the queen, and the canonical form of the reply has a row
   with depth `≤ d − 1`.
Plus coverage: every well-formed WTM state's canonical form has a row (can be done by
enumerating the 10 × 64 × 64 canonical candidates).
Soundness: by induction on `d`, a row of depth `d` gives `ForcesMate White d` for the canonical
state, transported by symmetry to every state.

**Symmetry justification.** Prove once (hand lemmas) that the 3 generators — file flip
`f ↦ 7−f`, rank flip `r ↦ 7−r`, transpose `(f,r) ↦ (r,f)` — map `legalMoves` of a pawnless,
castling-free position bijectively onto those of the image, and preserve `inCheck`,
`isCheckmate`, `isStalemate`, hence `ForcesMate`. The rank flip and transpose are *not*
symmetries of general chess (pawn direction, castling), so the lemma must be stated for positions
without pawns and castling rights. Alternative avoiding symmetry lemmas: certify all 144 508 WTM
states directly (8× more work, no symmetry proof) — a reasonable first version if kernel cost
permits.

**Size and cost estimate (rough).** With symmetry: 18 081 rows, 53 384 Black replies to check
(max 8 per row), each reply needing a canonicalisation (8 transforms) and a table lookup:
~0.5 M elementary square operations plus ~53 k lookups, plus 18 081 legality checks of the
certified move. Without symmetry: 144 508 rows, 425 502 replies. Kernel cost is dominated by the
move generator (`legalMoves` in `Rules.lean` is generic, list-based, with `Int` shifts) and by
lookups: a single huge `Nat` literal is a bad table (each shift/mask is linear in its size);
use a two-level structure (e.g. 64 chunk literals per `wk`, or a balanced tree of `Nat`
literals of ~1–4 KB). Likely feasible in seconds to minutes if a specialised KQK move generator
is proved equal to `legalMoves` on KQK positions; with the generic generator, expect a large
constant factor — measure on a slice (e.g. one `wk` square) first. These are guesses, not
measurements.

## Artifact index

- `log.md` — dated log.
- `computations/kqk_retro.py` — oracle (retrograde analysis, writes tables and summary).
- `computations/kqk_validate.py` — independent validator (checks V1–V5).
- `computations/cert_size.py` — certificate sizes, principal variation.
- `computations/kqk_summary.json`, `run_kqk_retro.out` — counts and distributions.
- `computations/kqk_wtm.tsv` — all WTM states: `wk wq bk dtm src dst`.
- `computations/kqk_btm.tsv` — all BTM states: `wk wq bk value` (`n`, `M0`, `S`, `C`).
- `computations/kqk_wtm_canonical_cert.tsv` — candidate certificate (18 081 canonical rows).
- `computations/run_kqk_validate.out`, `computations/run_cert_size.out` — check outputs.

Reproduce: `cd computations && ../../../../.venv-ws/bin/python kqk_retro.py && ../../../../.venv-ws/bin/python kqk_validate.py && ../../../../.venv-ws/bin/python cert_size.py` (~45 s total).
