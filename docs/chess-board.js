/* Chess board widget for the Chess-in-Lean site and slides.
 *
 *   ChessBoard(el, scene) -> { setActive(on), reset(), state() }
 *
 * Two kinds of scene:
 *   line: { fen, turn, moves: ["f2f3", ...], captions: [...], loop, speed }
 *         steps through a fixed sequence of moves (the fixtures of the Lean sanity suites);
 *   kqk:  { mode: "kqk", kqk: { wk: "a1", wq: "b2", bk: "f5" } }
 *         king and queen against king: White plays the move of the table checked by the Lean
 *         kernel (KQKData.lean, via kqk-table.js); Black plays the longest defence, or the
 *         viewer plays Black by clicking the black king and a target square.
 * Squares are indexed 8 * rank + file with a1 = 0, as in the Lean kernel.
 */
(function () {
  "use strict";
  const GLYPH = { k: "♚", q: "♛", r: "♜", b: "♝", n: "♞", p: "♟" };
  const FILES = "abcdefgh";

  const sqIdx = (s) => FILES.indexOf(s[0]) + 8 * (parseInt(s[1], 10) - 1);
  const sqName = (i) => FILES[i % 8] + (Math.floor(i / 8) + 1);
  const fileOf = (i) => i % 8;
  const rankOf = (i) => Math.floor(i / 8);

  /* ---------- positions and moves (fixture replay) ---------- */
  function parseFen(fen) {
    const b = new Array(64).fill(null);
    const rows = fen.split(" ")[0].split("/");
    rows.forEach((row, r) => {
      let f = 0;
      for (const ch of row) {
        if (/\d/.test(ch)) { f += parseInt(ch, 10); continue; }
        const white = ch === ch.toUpperCase();
        b[8 * (7 - r) + f] = { c: white ? "w" : "b", t: ch.toLowerCase() };
        f++;
      }
    });
    return b;
  }

  /* The effect of a move, as `play` in Kernel/Chess/Rules.lean: promotion, en passant capture
     (a pawn moving diagonally onto an empty square) and the rook's castling move. */
  function applyMove(board, uci) {
    const b = board.slice();
    const from = sqIdx(uci.slice(0, 2)), to = sqIdx(uci.slice(2, 4));
    const pc = b[from];
    if (!pc) return { board: b, from, to, capture: false };
    let capture = !!b[to];
    if (pc.t === "p" && fileOf(from) !== fileOf(to) && !b[to]) {
      const victim = to + (pc.c === "w" ? -8 : 8);
      b[victim] = null; capture = true;
    }
    if (pc.t === "k" && Math.abs(fileOf(to) - fileOf(from)) === 2) {
      const r = rankOf(from);
      if (fileOf(to) === 6) { b[8 * r + 5] = b[8 * r + 7]; b[8 * r + 7] = null; }
      else { b[8 * r + 3] = b[8 * r + 0]; b[8 * r + 0] = null; }
    }
    b[to] = uci.length > 4 ? { c: pc.c, t: uci[4] } : pc;
    b[from] = null;
    return { board: b, from, to, capture };
  }

  /* ---------- king and queen against king (the certified table) ---------- */
  let TABLE = null;
  function table() {
    if (TABLE) return TABLE;
    if (!window.KQK_TABLE_B64) return null;
    const bin = atob(window.KQK_TABLE_B64);
    const dv = new DataView(new ArrayBuffer(bin.length));
    for (let i = 0; i < bin.length; i++) dv.setUint8(i, bin.charCodeAt(i));
    TABLE = new Uint16Array(bin.length / 2);
    for (let i = 0; i < TABLE.length; i++) TABLE[i] = dv.getUint16(2 * i, true);
    return TABLE;
  }
  const KQK = {
    entry(wk, wq, bk) {
      const t = table(); if (!t) return null;
      const e = t[4096 * wk + 64 * wq + bk];
      return { raw: e, depth: e % 16, src: (e >> 4) % 64, dst: (e >> 10) % 64 };
    },
    adj(a, b) {
      return a !== b && Math.abs(fileOf(a) - fileOf(b)) <= 1 && Math.abs(rankOf(a) - rankOf(b)) <= 1;
    },
    /* does the queen on q attack square s, with `block` the occupied squares? */
    queenAttacks(q, s, block) {
      if (q === s) return false;
      const df = Math.sign(fileOf(s) - fileOf(q)), dr = Math.sign(rankOf(s) - rankOf(q));
      const lf = Math.abs(fileOf(s) - fileOf(q)), lr = Math.abs(rankOf(s) - rankOf(q));
      if (!(lf === 0 || lr === 0 || lf === lr)) return false;
      let f = fileOf(q) + df, r = rankOf(q) + dr;
      while (8 * r + f !== s) {
        if (block.includes(8 * r + f)) return false;
        f += df; r += dr;
      }
      return true;
    },
    blackInCheck(st) { return KQK.queenAttacks(st.wq, st.bk, [st.wk]); },
    blackMoves(st) {
      const out = [];
      for (let df = -1; df <= 1; df++) for (let dr = -1; dr <= 1; dr++) {
        if (!df && !dr) continue;
        const f = fileOf(st.bk) + df, r = rankOf(st.bk) + dr;
        if (f < 0 || f > 7 || r < 0 || r > 7) continue;
        const t = 8 * r + f;
        if (t === st.wk || KQK.adj(t, st.wk)) continue;
        if (t === st.wq) { out.push(t); continue; }      // capture of an undefended queen
        if (KQK.queenAttacks(st.wq, t, [st.wk])) continue;
        out.push(t);
      }
      return out;
    }
  };

  /* ---------- the widget ---------- */
  function ChessBoard(el, scene) {
    el.innerHTML = "";
    el.classList.add("cb");
    const boardEl = document.createElement("div"); boardEl.className = "cb-board";
    const sqEls = [];
    for (let r = 7; r >= 0; r--) for (let f = 0; f < 8; f++) {
      const d = document.createElement("div");
      const i = 8 * r + f;
      d.className = "cb-sq " + ((f + r) % 2 ? "cb-light" : "cb-dark");
      d.dataset.sq = i;
      if (f === 0) { const l = document.createElement("span"); l.className = "cb-rk"; l.textContent = r + 1; d.appendChild(l); }
      if (r === 0) { const l = document.createElement("span"); l.className = "cb-fl"; l.textContent = FILES[f]; d.appendChild(l); }
      const p = document.createElement("span"); p.className = "cb-pc"; d.appendChild(p);
      sqEls[i] = d; boardEl.appendChild(d);
    }
    el.appendChild(boardEl);
    const cap = document.createElement("div"); cap.className = "cb-cap"; el.appendChild(cap);
    const bar = document.createElement("div"); bar.className = "cb-bar"; el.appendChild(bar);
    const kqkMode = scene.mode === "kqk";
    const speed = scene.speed || (kqkMode ? 900 : 1100);
    let active = false, timer = null, playing = !!scene.autoplay;
    let ply = 0, frames = [], sel = null;

    function btn(label, title, fn, cls) {
      const b = document.createElement("button");
      b.className = "cb-btn" + (cls ? " " + cls : ""); b.textContent = label; b.title = title;
      b.addEventListener("click", fn); bar.appendChild(b); return b;
    }
    const status = document.createElement("span"); status.className = "cb-status";

    /* frames: [{board, from, to, caption, status}] */
    function buildLine() {
      let b = parseFen(scene.fen), turn = scene.turn || "w";
      frames = [{ board: b, from: -1, to: -1, turn }];
      (scene.moves || []).forEach((m) => {
        const r = applyMove(b, m); b = r.board; turn = turn === "w" ? "b" : "w";
        frames.push({ board: b, from: r.from, to: r.to, turn, move: m });
      });
    }
    function kqkFrame(st, from, to) {
      const b = new Array(64).fill(null);
      b[st.wk] = { c: "w", t: "k" }; b[st.wq] = { c: "w", t: "q" }; b[st.bk] = { c: "b", t: "k" };
      if (st.captured) b[st.wq] = null, b[st.bk] = { c: "b", t: "k" };
      return { board: b, from, to, st: Object.assign({}, st) };
    }
    function kqkStart(pos) {
      const st = { wk: sqIdx(pos.wk), wq: sqIdx(pos.wq), bk: sqIdx(pos.bk), turn: pos.turn || "w", over: null };
      frames = [kqkFrame(st, -1, -1)]; ply = 0; kqkStatus(); render();
    }
    function kqkStatus() {
      const st = frames[ply].st;
      if (st.over) return;
      if (st.turn === "b") {
        const ms = KQK.blackMoves(st);
        if (!ms.length) st.over = KQK.blackInCheck(st) ? "mate" : "stalemate";
      } else {
        const e = KQK.entry(st.wk, st.wq, st.bk);
        if (!e || !e.depth) st.over = "noentry";
      }
    }
    function kqkPush(st, from, to) {
      frames = frames.slice(0, ply + 1);
      frames.push(kqkFrame(st, from, to)); ply++; kqkStatus(); render();
    }
    function kqkWhite() {
      const st = Object.assign({}, frames[ply].st);
      const e = KQK.entry(st.wk, st.wq, st.bk);
      if (!e || !e.depth) return false;
      if (e.src === st.wk) st.wk = e.dst; else st.wq = e.dst;
      st.turn = "b"; st.over = null;
      kqkPush(st, e.src, e.dst); return true;
    }
    function kqkBlack(target) {
      const st = Object.assign({}, frames[ply].st);
      const ms = KQK.blackMoves(st);
      if (!ms.length) return false;
      let t = target;
      if (t === undefined) {        // longest defence: the reply of largest certified depth
        let best = -1;
        for (const m of ms) {
          if (m === st.wq) { t = m; break; }
          const e = KQK.entry(st.wk, st.wq, m);
          if (e && e.depth > best) { best = e.depth; t = m; }
        }
      }
      if (!ms.includes(t)) return false;
      const from = st.bk;
      if (t === st.wq) { st.captured = true; st.over = "captured"; }
      st.bk = t; st.turn = "w";
      kqkPush(st, from, t); return true;
    }
    function step() {
      if (kqkMode) {
        if (ply < frames.length - 1) { ply++; render(); return true; }
        const st = frames[ply].st;
        if (st.over) return false;
        return st.turn === "w" ? kqkWhite() : kqkBlack();
      }
      if (ply < frames.length - 1) { ply++; render(); return true; }
      if (scene.loop) { ply = 0; render(); return true; }
      return false;
    }
    function back() { if (ply > 0) { ply--; sel = null; render(); } }
    function restart() { ply = 0; sel = null; render(); }
    function tick() {
      clearTimeout(timer);
      if (!active || !playing) return;
      timer = setTimeout(() => {
        const moved = step();
        if (!moved) {
          if (kqkMode && scene.loop) { setTimeout(() => { kqkStart(scene.kqk); tick(); }, 1600); return; }
          playing = false; updateBar(); return;
        }
        tick();
      }, (kqkMode && frames[ply] && frames[ply].st.over) ? 1600 : speed);
    }
    let playBtn = null;
    function updateBar() { if (playBtn) playBtn.textContent = playing ? "❚❚" : "▶"; }

    if (scene.controls !== false) {
      btn("⏮", "Back to the start", () => { playing = false; updateBar(); restart(); });
      btn("◀", "Back one move", () => { playing = false; updateBar(); back(); });
      playBtn = btn("▶", "Play / pause", () => { playing = !playing; updateBar(); tick(); }, "cb-play");
      btn("▶|", "Forward one move", () => { playing = false; updateBar(); step(); });
      if (kqkMode) {
        btn("Longest", "The position needing the full 10 moves", () => {
          playing = false; updateBar(); kqkStart({ wk: "a1", wq: "b2", bk: "f5" });
        });
        btn("Random", "A random position with White to move", () => {
          playing = false; updateBar();
          const t = table(); if (!t) return;
          for (;;) {
            const i = Math.floor(Math.random() * 262144);
            if (t[i] % 16) { kqkStart({ wk: sqName(i >> 12), wq: sqName((i >> 6) & 63), bk: sqName(i & 63) }); break; }
          }
        });
      }
      bar.appendChild(status);
    } else bar.style.display = "none";

    if (kqkMode) {
      boardEl.addEventListener("click", (ev) => {
        const d = ev.target.closest(".cb-sq"); if (!d) return;
        const i = +d.dataset.sq, st = frames[ply].st;
        if (st.over || st.turn !== "b") return;
        if (sel === null) { if (i === st.bk) { sel = i; render(); } return; }
        const ok = KQK.blackMoves(st).includes(i);
        sel = null;
        if (ok) { playing = false; updateBar(); kqkBlack(i); setTimeout(() => { if (!frames[ply].st.over) kqkWhite(); }, 450); }
        else render();
      });
    }

    function render() {
      const fr = frames[ply];
      for (let i = 0; i < 64; i++) {
        const d = sqEls[i], pc = fr.board[i], p = d.querySelector(".cb-pc");
        p.textContent = pc ? GLYPH[pc.t] : "";
        p.className = "cb-pc" + (pc ? (pc.c === "w" ? " cb-w" : " cb-b") : "");
        d.classList.toggle("cb-last", i === fr.from || i === fr.to);
        d.classList.toggle("cb-mark", (scene.marks || []).includes(sqName(i)) && ply === 0);
        d.classList.toggle("cb-sel", sel === i);
        d.classList.toggle("cb-target", false);
      }
      if (kqkMode) {
        const st = fr.st;
        if (sel !== null) KQK.blackMoves(st).forEach((t) => sqEls[t].classList.add("cb-target"));
        const e = st.turn === "w" ? KQK.entry(st.wk, st.wq, st.bk) : null;
        let s;
        if (st.over === "mate") s = "Checkmate: the certified line ends here.";
        else if (st.over === "stalemate") s = "Stalemate.";
        else if (st.over === "captured") s = "Black captured the queen: K v K, a dead position.";
        else if (st.over === "noentry") s = "No table entry (not a legal White-to-move position).";
        else if (st.turn === "w") s = "White to move: mate within " + e.depth + " (certified).";
        else s = "Black to move" + (KQK.blackInCheck(st) ? " (in check)" : "") +
          (scene.controls !== false ? ": click the black king to play Black." : ".");
        status.textContent = s;
        cap.textContent = scene.captions && ply === 0 ? scene.captions[0] : "";
        if (scene.onState) scene.onState(st, e);
      } else {
        const n = frames.length - 1;
        status.textContent = n ? "move " + ply + " / " + n : "";
        const c = scene.captions || [];
        cap.textContent = c[ply] !== undefined ? c[ply] : (c.length ? c[c.length - 1] : "");
      }
      cap.style.display = cap.textContent ? "" : "none";
    }

    if (kqkMode) kqkStart(scene.kqk); else { buildLine(); render(); }
    updateBar();
    return {
      setActive(on) { active = on; if (on) { if (scene.autoplay) playing = true; updateBar(); tick(); } else clearTimeout(timer); },
      reset() { if (kqkMode) kqkStart(scene.kqk); else restart(); },
      state() { return frames[ply]; }
    };
  }
  ChessBoard.KQK = KQK;
  ChessBoard.applyMove = applyMove;
  ChessBoard.parseFen = parseFen;
  ChessBoard.sqIdx = sqIdx;
  ChessBoard.sqName = sqName;
  window.ChessBoard = ChessBoard;
})();
