#!/usr/bin/env python3
"""KQK retrograde analysis (N-06).  UNTRUSTED exploratory computation.

Square convention (matches LeanTheory/Kernel/Chess/Rules.lean): Square = Fin 64,
index 8*rank + file, a1 = 0, h1 = 7, a8 = 56.

State = (wk, wq, bk, stm) with stm 0 = White to move, 1 = Black to move.
State index  = ((wk*64 + wq)*64 + bk)*2 + stm.

Values:
  White to move: DTM = number of White moves to mate (>= 1), or None if not won.
  Black to move: 'M0' already checkmated, 'S' stalemate, 'C' Black can capture the queen
  (FIDE: Black is not forced to, so the state is a draw if the capture is legal),
  otherwise mate in n = max over Black replies of the White-to-move DTM.

Outputs (in this directory):
  kqk_wtm.tsv   wk wq bk dtm best_move_src best_move_dst   (all well-formed WTM states)
  kqk_btm.tsv   wk wq bk value                             (all well-formed BTM states)
  kqk_summary.json
"""
import json, os, sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))

def fr(s): return s % 8, s // 8
def name(s): f, r = fr(s); return "abcdefgh"[f] + str(r + 1)

KDIRS = [(1,0),(1,1),(0,1),(-1,1),(-1,0),(-1,-1),(0,-1),(1,-1)]
QDIRS = KDIRS

def shift(s, df, dr):
    f, r = fr(s); f += df; r += dr
    return r*8+f if 0 <= f < 8 and 0 <= r < 8 else None

KING_NB = [[t for d in KDIRS if (t := shift(s, *d)) is not None] for s in range(64)]
ADJ = [[False]*64 for _ in range(64)]
for s in range(64):
    for t in KING_NB[s]: ADJ[s][t] = True
# rays[s][d] = list of squares from s outward in direction d
RAYS = [[[] for _ in QDIRS] for _ in range(64)]
for s in range(64):
    for i, d in enumerate(QDIRS):
        t = s
        while (t := shift(t, *d)) is not None: RAYS[s][i].append(t)

def queen_attacks(q, target, blockers):
    """Does a queen on q attack `target`, rays stopped by squares in `blockers`?"""
    for ray in RAYS[q]:
        for t in ray:
            if t == target: return True
            if t in blockers: break
    return False

def idx(wk, wq, bk, stm): return ((wk*64+wq)*64+bk)*2+stm

def well_formed(wk, wq, bk, stm):
    if len({wk, wq, bk}) < 3 or ADJ[wk][bk]: return False
    if stm == 0 and queen_attacks(wq, bk, {wk}): return False  # side not to move (Black) in check
    return True   # White king can only be attacked by the black king (adjacency excluded)

def white_moves(wk, wq, bk):
    """Legal White moves, as (src, dst, resulting BTM state tuple)."""
    out = []
    for t in KING_NB[wk]:
        if t != wq and t != bk and not ADJ[t][bk]:
            out.append((wk, t, (t, wq, bk)))
    for ray in RAYS[wq]:
        for t in ray:
            if t == wk or t == bk: break   # cannot capture the king; blocked
            out.append((wq, t, (wk, t, bk)))
    return out

def black_moves(wk, wq, bk):
    """Legal Black moves: list of (dst, kind) with kind 'cap' (takes queen) or WTM state tuple."""
    out = []
    for t in KING_NB[bk]:
        if t == wk or ADJ[t][wk]: continue
        if t == wq:
            out.append((t, 'cap'))          # queen undefended (not adjacent to wk) -> legal capture
            continue
        if queen_attacks(wq, t, {wk}): continue  # bk does not block (x-ray through its old square)
        out.append((t, (wk, wq, t)))
    return out

def black_in_check(wk, wq, bk): return queen_attacks(wq, bk, {wk})

# ---------- symmetry ----------
def tf(s, k):
    f, r = fr(s)
    if k & 1: f = 7 - f
    if k & 2: r = 7 - r
    if k & 4: f, r = r, f
    return r*8+f
def canon(wk, wq, bk):
    return min((tf(wk,k), tf(wq,k), tf(bk,k)) for k in range(8))

def main():
    W = {}   # (wk,wq,bk) -> list of moves for WTM states
    B = {}
    for wk in range(64):
        for wq in range(64):
            for bk in range(64):
                if well_formed(wk, wq, bk, 0): W[(wk,wq,bk)] = white_moves(wk,wq,bk)
                if well_formed(wk, wq, bk, 1): B[(wk,wq,bk)] = black_moves(wk,wq,bk)
    # sanity: successors are well formed
    for s, ms in W.items():
        for _,_,t in ms: assert t in B, (s, t)
    for s, ms in B.items():
        for _,t in ms:
            if t != 'cap': assert t in W, (s, t)

    bval = {}   # BTM: 'M0','S','C', or int n
    for s, ms in B.items():
        if not ms: bval[s] = 'M0' if black_in_check(*s) else 'S'
        elif any(t == 'cap' for _,t in ms): bval[s] = 'C'
    dtm = {}; best = {}
    n = 0
    while True:
        n += 1
        new = {}
        for s, ms in W.items():
            if s in dtm: continue
            # best: a move to a BTM state with value M0 or int <= n-1; prefer smallest
            cand = None
            for src, dst, t in ms:
                v = bval.get(t)
                v = 0 if v == 'M0' else v
                if isinstance(v, int) and v <= n-1 and (cand is None or v < cand[0]):
                    cand = (v, src, dst)
            if cand: new[s] = cand
        if not new: break
        for s, c in new.items(): dtm[s] = n; best[s] = (c[1], c[2])
        for s, ms in B.items():
            if s in bval: continue
            vals = [dtm.get(t) for _,t in ms]
            if all(v is not None for v in vals): bval[s] = max(vals)
    # unresolved BTM states (never fully resolved) get 'D?' (would indicate a non-won state)
    for s in B:
        if s not in bval: bval[s] = 'D?'

    # ---------- statistics ----------
    nW, nB = len(W), len(B)
    cW = {canon(*s) for s in W}; cB = {canon(*s) for s in B}
    won = len(dtm); maxd = max(dtm.values())
    distW = Counter(dtm.values())
    distW_c = Counter(dtm[s] for s in cW)
    bcls = Counter('mate-in-n' if isinstance(v, int) else v for v in bval.values())
    bcls_c = Counter('mate-in-n' if isinstance(bval[s], int) else bval[s] for s in cB)
    distB = Counter(v for v in bval.values() if isinstance(v, int))
    distB_c = Counter(bval[s] for s in cB if isinstance(bval[s], int))
    # symmetry consistency of dtm
    for s in W:
        c = canon(*s); assert dtm.get(s) == dtm.get(c)
    for s in B:
        assert bval[s] == bval[canon(*s)]
    nrepl = sum(len(B[(t)]) for s in cW for (_,_,t) in [next(m for m in W[s] if (m[0],m[1]) == best[s])])
    maxrepl = max(len(B[t]) for s in cW for (_,_,t) in [next(m for m in W[s] if (m[0],m[1]) == best[s])])
    examples = sorted((s for s in cW if dtm.get(s) == maxd))
    summary = dict(
        wtm_states=nW, btm_states=nB, total_states=nW+nB,
        wtm_canonical=len(cW), btm_canonical=len(cB),
        wtm_won=won, wtm_not_won=nW-won, max_dtm_wtm=maxd,
        dtm_distribution_wtm={k: distW[k] for k in sorted(distW)},
        dtm_distribution_wtm_canonical={k: distW_c[k] for k in sorted(distW_c)},
        btm_classes=dict(bcls), btm_classes_canonical=dict(bcls_c),
        btm_mate_in_n_distribution={k: distB[k] for k in sorted(distB)},
        btm_mate_in_n_distribution_canonical={k: distB_c[k] for k in sorted(distB_c)},
        max_btm_mate_in=max(distB),
        certificate_black_replies_total_canonical=nrepl,
        certificate_max_black_replies=maxrepl,
        wtm_white_moves_total=sum(len(m) for m in W.values()),
        btm_black_moves_total=sum(len(m) for m in B.values()),
        max_dtm_examples_canonical=[(name(a), name(b), name(c)) for a,b,c in examples[:20]],
        max_dtm_examples_count_canonical=len(examples),
    )
    with open(os.path.join(HERE, 'kqk_summary.json'), 'w') as f: json.dump(summary, f, indent=1)
    with open(os.path.join(HERE, 'kqk_wtm.tsv'), 'w') as f:
        f.write('# wk\twq\tbk\tdtm\tsrc\tdst   (squares 0..63, a1=0, h1=7, a8=56; dtm in White moves)\n')
        for s in sorted(W):
            d = dtm.get(s); b = best.get(s, (-1,-1))
            f.write(f'{s[0]}\t{s[1]}\t{s[2]}\t{d if d else -1}\t{b[0]}\t{b[1]}\n')
    with open(os.path.join(HERE, 'kqk_btm.tsv'), 'w') as f:
        f.write('# wk\twq\tbk\tvalue   (int n = White mates in n White moves; M0 checkmated; S stalemate; C queen capturable)\n')
        for s in sorted(B): f.write(f'{s[0]}\t{s[1]}\t{s[2]}\t{bval[s]}\n')
    with open(os.path.join(HERE, 'kqk_wtm_canonical_cert.tsv'), 'w') as f:
        f.write('# canonical WTM states (lexicographic min of (wk,wq,bk) over 8 symmetries): wk wq bk dtm src dst\n')
        for s in sorted(cW): f.write(f'{s[0]}\t{s[1]}\t{s[2]}\t{dtm[s]}\t{best[s][0]}\t{best[s][1]}\n')
    print(json.dumps(summary, indent=1))

if __name__ == '__main__':
    main()
