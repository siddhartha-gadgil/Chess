#!/usr/bin/env python3
"""Independent validator for K+X vs K tables (`kxk_validate.py R` for KRK; X is labelled Q in the
code). Generalised from notes/reasoning/2026-11-20-kqk-oracle/computations/kqk_validate.py.  UNTRUSTED.

Written with a different board representation (0x88 mailbox + generic piece lists) and a
generic legality test (make the move, then ask whether the mover's king is attacked by ANY
enemy piece, including the enemy king), so that the shortcuts of kqk_retro.py (white king never
in check except by adjacency, x-ray handling) are re-derived rather than reused.

Checks:
 V1  the set of well-formed states (side not to move not in check, kings not adjacent,
     distinct squares) equals the set of rows in kqk_wtm.tsv / kqk_btm.tsv;
 V2  every BTM value satisfies its defining equation: M0 <=> no legal move and in check;
     S <=> no legal move and not in check; C <=> Black has a legal capture of the queen;
     int n <=> n = max over Black replies of the WTM dtm (all replies non-capturing);
 V3  for every WTM state of dtm d: the stored move is legal, and after it Black is either
     checkmated (then d = 1) or every Black reply is a non-capture leading to dtm <= d-1;
 V4  minimality: no legal White move leads to M0 when d > 1, nor to a BTM value < d-1;
 V5  every WTM state has a finite dtm (no draws with White to move).
V3 + V5 alone already imply (by induction on d) that the stored strategy mates within d moves
in this three-piece model; V2/V4 additionally confirm the depths are exact.
"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))

def to88(s): return (s // 8) * 16 + (s % 8)
def from88(x): return (x >> 4) * 8 + (x & 7)
KING = (-17, -16, -15, -1, 1, 15, 16, 17)
PIECE = sys.argv[1] if len(sys.argv) > 1 else 'Q'
QUEEN = KING if PIECE == 'Q' else (-16, -1, 1, 16)
PFX = 'kqk' if PIECE == 'Q' else 'krk'

def attacked(board, x, by):
    """Is 0x88 square x attacked by colour `by` ('w'/'b') on board (dict sq88 -> piece str)?"""
    for y, p in board.items():
        if p[0] != by: continue
        if p[1] == 'K':
            if x - y in KING: return True
        elif p[1] == 'Q':
            for d in QUEEN:
                z = y + d
                while not (z & 0x88):
                    if z == x: return True
                    if z in board: break
                    z += d
    return False

def kingsq(board, c):
    return next(y for y, p in board.items() if p == c + 'K')

def pseudo(board, c):
    for y, p in list(board.items()):
        if p[0] != c: continue
        slide = p[1] == 'Q'
        for d in (QUEEN if slide else KING):
            z = y + d
            while not (z & 0x88):
                q = board.get(z)
                if q is not None:
                    if q[0] != c and q[1] != 'K': yield (y, z)   # kings are never captured
                    break
                yield (y, z)
                if not slide: break
                z += d

def legal(board, c):
    other = 'b' if c == 'w' else 'w'
    out = []
    for y, z in pseudo(board, c):
        nb = dict(board); nb[z] = nb.pop(y)
        if not attacked(nb, kingsq(nb, c), other): out.append((y, z, nb))
    return out

def mkboard(wk, wq, bk):
    return {to88(wk): 'wK', to88(wq): 'wQ', to88(bk): 'bK'}

def key(nb):
    inv = {p: from88(y) for y, p in nb.items()}
    return (inv['wK'], inv.get('wQ'), inv['bK'])

def main():
    W = {}; B = {}
    with open(os.path.join(HERE, PFX + '_wtm.tsv')) as f:
        for line in f:
            if line.startswith('#'): continue
            a = list(map(int, line.split())); W[tuple(a[:3])] = (a[3], a[4], a[5])
    with open(os.path.join(HERE, PFX + '_btm.tsv')) as f:
        for line in f:
            if line.startswith('#'): continue
            a = line.split(); v = a[3]
            B[tuple(map(int, a[:3]))] = int(v) if v.lstrip('-').isdigit() else v
    errs = []
    # V1
    wf = {0: set(), 1: set()}
    for wk in range(64):
        for wq in range(64):
            for bk in range(64):
                if len({wk, wq, bk}) < 3: continue
                bd = mkboard(wk, wq, bk)
                if to88(bk) - to88(wk) in KING: continue
                if not attacked(bd, to88(bk), 'w'): wf[0].add((wk, wq, bk))
                if not attacked(bd, to88(wk), 'b'): wf[1].add((wk, wq, bk))
    if wf[0] != set(W): errs.append('V1 WTM set mismatch')
    if wf[1] != set(B): errs.append('V1 BTM set mismatch')
    print('V1 done', len(wf[0]), len(wf[1]))
    # V2
    for s, v in B.items():
        bd = mkboard(*s)
        ms = legal(bd, 'b'); chk = attacked(bd, to88(s[2]), 'w')
        caps = [m for m in ms if 'wQ' not in m[2].values()]
        if not ms: exp = 'M0' if chk else 'S'
        elif caps: exp = 'C'
        else: exp = max(W[key(nb)][0] for _, _, nb in ms)
        if exp != v: errs.append(('V2', s, v, exp))
    print('V2 done')
    # V3, V4, V5
    for s, (d, src, dst) in W.items():
        if d < 1: errs.append(('V5', s)); continue
        bd = mkboard(*s)
        ms = legal(bd, 'w')
        chosen = [nb for y, z, nb in ms if from88(y) == src and from88(z) == dst]
        if len(chosen) != 1: errs.append(('V3 illegal move', s, src, dst)); continue
        nb = chosen[0]; replies = legal(nb, 'b')
        if not replies:
            if not (attacked(nb, kingsq(nb, 'b'), 'w') and d == 1): errs.append(('V3 mate/stalemate', s))
        else:
            for _, _, nb2 in replies:
                k = key(nb2)
                if k[1] is None: errs.append(('V3 capture', s)); break
                if W[k][0] > d - 1: errs.append(('V3 depth', s, k)); break
        for _, _, nb in ms:
            v = B[key(nb)]
            if v == 'M0' and d > 1: errs.append(('V4 missed mate', s))
            if isinstance(v, int) and v < d - 1: errs.append(('V4 shorter', s))
    print('V3-V5 done')
    print('ERRORS:', len(errs)); print(errs[:20])
    return 1 if errs else 0

if __name__ == '__main__':
    sys.exit(main())
