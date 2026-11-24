"""Write docs/kqk-table.js from LeanTheory/Certificates/Chess/KQKData.lean.

The website plays exactly the table that the Lean kernel checked: the 64 hex literals
`kqkRow{wk}` are decoded into 262144 16-bit entries (entry = depth + 16*src + 1024*dst,
index = 4096*wk + 64*wq + bk) and stored as base64 little-endian uint16.
"""
import base64, re, struct, sys, pathlib
root = pathlib.Path(sys.argv[1])
src = (root / 'LeanTheory/Certificates/Chess/KQKData.lean').read_text()
rows = {int(m.group(1)): int(m.group(2), 16)
        for m in re.finditer(r'def kqkRow(\d+) : Nat := 0x([0-9a-f]+)', src)}
assert sorted(rows) == list(range(64))
entries = []
for wk in range(64):
    r = rows[wk]
    for j in range(4096):
        entries.append((r >> (16 * j)) & 0xFFFF)
n = sum(1 for e in entries if e % 16)
assert n == 144508, n
data = base64.b64encode(struct.pack('<%dH' % len(entries), *entries)).decode()
out = ('/* KQK table checked by the Lean kernel (generated from KQKData.lean by\n'
       '   notes/reasoning/2026-11-20-kqk-oracle/computations/gen_web_table.py).\n'
       '   Entry i = 4096*wk + 64*wq + bk: depth + 16*src + 1024*dst; depth 0 = no entry. */\n'
       'window.KQK_TABLE_B64 = "' + data + '";\n')
(root / 'docs/kqk-table.js').write_text(out)
print('entries with depth:', n, 'bytes:', len(out))
