"""Write docs/krk-table.js from LeanTheory/Certificates/Chess/KRKData.lean.

The website plays the KRK table that the Lean kernel checks: the 64 hex literals `krkRow{wk}`
hold 32-bit entries (entry = depth + 32*src + 2048*dst, index = 4096*wk + 64*wr + bk); entries
are below 2^17 and are stored here as 3 little-endian bytes each, in base64.
"""
import base64, re, sys, pathlib
root = pathlib.Path(sys.argv[1])
src = (root / 'LeanTheory/Certificates/Chess/KRKData.lean').read_text()
rows = {int(m.group(1)): int(m.group(2), 16)
        for m in re.finditer(r'def krkRow(\d+) : Nat := 0x([0-9a-f]+)', src)}
assert sorted(rows) == list(range(64))
buf = bytearray()
n = 0
for wk in range(64):
    r = rows[wk]
    for j in range(4096):
        e = (r >> (32 * j)) & 0xFFFFFFFF
        assert e < 1 << 24
        n += 1 if e % 32 else 0
        buf += bytes((e & 255, (e >> 8) & 255, (e >> 16) & 255))
assert n == 175168, n
out = ('/* KRK table checked by the Lean kernel (generated from KRKData.lean by\n'
       '   notes/reasoning/2026-11-24-krk/computations/gen_web_krk_table.py).\n'
       '   Entry i = 4096*wk + 64*wr + bk, 3 bytes: depth + 32*src + 2048*dst; depth 0 = no entry. */\n'
       'window.KRK_TABLE_B64 = "' + base64.b64encode(bytes(buf)).decode() + '";\n')
(root / 'docs/krk-table.js').write_text(out)
print('entries with depth:', n, 'bytes:', len(out))
