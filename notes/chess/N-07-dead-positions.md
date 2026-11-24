# N-07 — Dead positions and insufficient material

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-07` |
| Title | KvK, KBvK, KNvK are dead; KQvK is not |
| Kind | proof / formalization |
| Addresses | `G-1`, `G-4`, `Q-6` |
| Depends on | `N-02`, `N-03` |
| Dependency requirement | Compiled `IsDead` defined semantically (no legal continuation reaches checkmate) |
| Produces | Theorems `dead_KK`, `dead_KBK`, `dead_KNK`, `not_dead_KQK` (planned) |
| Difficulty | moderate: "no checkmate is reachable" is a universal statement over sequences; proof is by an invariant (material can only decrease and the lone pieces cannot mate) |
| Status | **verified** (KvK, KNvK, KBvK) |
| Implementation status | complete |
| Implementation evidence | `LeanTheory/Theory/Chess/DeadPositions.lean`, `LeanTheory/Theory/Chess/DeadPositionsBishop.lean` |
| Lean evidence | `LeanTheory.Chess.{dead_KK, dead_KNK, not_dead_KQK_example, KKInv, KNInv, DInv.isDead, knk_flight}`; fixtures `kkPos_dead`, `kkPos_flags_dead`, `knkPos_dead`, `knkPosBlack_dead`, `adjacent_kings_not_wellFormed`, `kqkPos_not_onlyKings`, `kqkPos_not_kingsAndKnight` |
| Audit evidence | 2026-11-24: statements reviewed (sub-agent work); zero warnings, standard axioms only |
| Last updated | 2026-11-20: created at seeding |

## Purpose and scope

Sanity checks for Article 5.2.2 and a building block for endgame values: a KQK state in which
Black captures the queen becomes KvK and is drawn. `not_dead_KQK` guards against an over-broad
definition of `IsDead`; `dead_KK` guards against a vacuous one.

Caution (correction `C-2`): "insufficient material" is a sufficient, not a necessary, condition
for a dead position (blocked pawn chains can be dead with much material). Do not define `IsDead`
by material.

## Results

- `dead_KK (p) (hw : wellFormed p = true) (hk : onlyKings p.board = true) : IsDead p`.
- `dead_KNK (p) (c) (hw : wellFormed p = true) (hm : kingsAnd ⟨c, .knight⟩ p.board = true)
  (hn : countPiece p.board ⟨c, .knight⟩ = 1) : IsDead p` (knight of either colour).
- `not_dead_KQK_example`: a concrete KQK position is not dead (via a certified mate in one).
- Method: symbolic invariants closed under legal moves that exclude checkmate (`KKInv`, `KNInv`),
  by induction on move sequences; key geometric lemma `knk_flight` (a king checked by a lone
  knight always has a flight square). No enumeration. No assumption on castling flags, en
  passant field or halfmove clock.

- `dead_KBK (p) (c) (hw : wellFormed p = true) (hm : kingsAnd ⟨c, .bishop⟩ p.board = true)
  (hn : countPiece p.board ⟨c, .bishop⟩ = 1) : IsDead p` (sub-agent, 2026-11-24): invariant
  `DBInv := KKInv ∨ KBInv`; diagonal-colour lemma `firstOnRay_diag`, ray reversal
  `firstOnRay_of_mem_rayTargets` (the bishop never captures the lone king), flight square
  `kbk_flight`. Fixtures `kbkPos_dead`, `kbkPosBlack_dead`, `kbkPosCheck_dead` (check exercised),
  rejected `kbbkPos_two_bishops`, `kqkFixture_not_kingsAndBishop`.

## Readiness

Done for the three classical insufficient-material cases. Possible extensions: KB vs KB with
bishops on the same colour (also dead), and positions dead by blocked pawns. Former plan for KBvK: plan (sub-agent): `KBInv` with a diagonal-colour invariant for bishop rays and a
ray-reversal lemma (a bishop attacking the king implies the king's ray meets the bishop), reusing
`knk_flight_of` with the colour argument; ≈ 300 lines.
