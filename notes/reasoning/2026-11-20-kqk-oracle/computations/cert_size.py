#!/usr/bin/env python3
"""Certificate size estimates for N-05 route (b), from kqk_wtm.tsv (UNTRUSTED)."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from kqk_retro import black_moves, canon, name
HERE = os.path.dirname(os.path.abspath(__file__))
W = {}
for line in open(os.path.join(HERE, 'kqk_wtm.tsv')):
    if line.startswith('#'): continue
    a = list(map(int, line.split())); W[tuple(a[:3])] = a[3:]
def after(s, src, dst):
    wk, wq, bk = s
    return (dst, wq, bk) if src == wk else (wk, dst, bk)
tot = sum(len(black_moves(*after(s, v[1], v[2]))) for s, v in W.items())
C = sorted({canon(*s) for s in W})
totc = sum(len(black_moves(*after(s, W[s][1], W[s][2]))) for s in C)
kmoves = sum(1 for s in C if W[s][1] == s[0])
mates = [s for s in C if W[s][0] == 1]
print('full WTM states', len(W), 'black replies to certified moves', tot)
print('canonical WTM states', len(C), 'black replies', totc, 'king moves in cert', kmoves)
# canonical squares used by white king
print('distinct wk in canonical reps', sorted({name(s[0]) for s in C}))
# a principal line from the DTM-10 state
s = next(s for s in C if W[s][0] == 10)
line = []
while True:
    d, src, dst = W[s]
    t = after(s, src, dst)
    rs = black_moves(*t)
    line.append(f'{d}: W{"K" if src==s[0] else "Q"}{name(src)}-{name(dst)}')
    if not rs: line.append('mate'); break
    # black's longest-resisting reply
    best = max(rs, key=lambda r: W[r[1]][0]); s = best[1]
    line.append(f'BK-{name(best[0])}')
print(' '.join(line))
