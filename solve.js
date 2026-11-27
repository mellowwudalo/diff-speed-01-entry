// solve.js — an exact, faster reimplementation of the makefun-diff 1.0.0 patch rule.
//
// run(input) takes { old, new } (two texts) and returns the patch string the rule
// specifies: a header line, then hunks of kept/deleted/inserted lines with up to 3
// kept lines of context, change runs at most 6 kept lines apart sharing a hunk,
// deletions listed before insertions inside a run, and a "%" line after any line
// that ends its text without a newline.
//
// How it works, in outline:
//   1. Both texts are cut into lines after every "\n" (a "\r" stays part of its
//      line; a final piece with no "\n" is a line too) and every distinct line is
//      interned to a small integer, so all later comparisons are integer compares.
//   2. The common prefix and the common suffix of the remaining lines are kept.
//   3. Between them, Myers's greedy search runs exactly as the rule states: for
//      d = 0, 1, 2, ... and each diagonal k, the furthest-reaching path wins, a
//      deletion beats an insertion on a tie, no candidate may pass either text's
//      end, no edge diagonal is pruned, and every snake of equal lines is followed
//      to its end. The first path to reach both ends is the edit script.
//      The search stores each d's band of states (positions, plus which step
//      produced each state) in flat typed arrays, so the winning path is then
//      read back exactly, state by state, with no per-state objects allocated.
//      Only diagonals a path of d edits can sit on inside the two texts are
//      visited: a state on diagonal k has made (d+k)/2 deletions and (d-k)/2
//      insertions, so k also satisfies d-2m <= k <= 2n-d; any state outside
//      that band is one no path reaches, and skipping it is unobservable.
//   4. The script is grouped into change runs and hunks and written out.
//
// No dependencies; plain ES module, Node 22.

/** Kept lines of context a hunk shows around a change run. */
const CONTEXT = 3;

/** Segment kinds used while assembling the edit script. */
const KEEP = 0;
const DEL = 1;
const INS = 2;

/** Frontier value for a diagonal no path reaches at the current d (real values are >= -1). */
const UNREACH = -2;

/**
 * A text's lines: cut after every "\n"; the last piece is a line only when the
 * text does not end in "\n" (the empty text has no lines, "\n" has one).
 */
function splitLines(text) {
  const lines = [];
  let start = 0;
  let cut;
  while ((cut = text.indexOf('\n', start)) !== -1) {
    lines.push(text.slice(start, cut + 1));
    start = cut + 1;
  }
  if (start < text.length) lines.push(text.slice(start));
  return lines;
}

/**
 * The greedy Myers search over the middle slices a (n lines) and b (m lines) of
 * interned line ids. Appends the edit script to `seg` as flat [kind, count]
 * pairs in forward order, merging neighbours of a kind. Follows the rule's
 * choices exactly: furthest into the old text wins, deletion on a tie, the
 * first state (in d, then k, order) to reach both ends ends the search.
 *
 * Every d's band is stored compactly: bandBase[d] is the flat index of its
 * first state and bandLo[d] that state's diagonal, so a state's slot is
 * bandBase[d] + (k - bandLo[d]) / 2. bandX holds each state's old position
 * (the last old line it consumed), bandStep 1 when the state was reached by a
 * deletion step, 0 by an insertion step.
 */
function searchMiddle(a, n, b, m, seg) {
  let cap = 1 << 16;
  let bandX = new Int32Array(cap);
  let bandStep = new Uint8Array(cap);
  let bandLen = 0;
  const bandBase = [];
  const bandLo = [];
  const ensure = (need) => {
    if (need <= cap) return;
    while (cap < need) cap *= 2;
    const nx = new Int32Array(cap);
    nx.set(bandX);
    bandX = nx;
    const ns = new Uint8Array(cap);
    ns.set(bandStep);
    bandStep = ns;
  };

  // d = 0: the single state on diagonal 0, then its snake.
  let x = -1;
  let y = -1;
  while (x + 1 < n && y + 1 < m && a[x + 1] === b[y + 1]) {
    x++;
    y++;
  }
  bandBase.push(0);
  bandLo.push(0);
  bandX[0] = x;
  bandStep[0] = 0;
  bandLen = 1;
  let winD = -1;
  let winK = 0;
  if (x + 1 >= n && y + 1 >= m) winD = 0;

  const maxD = n + m;
  for (let d = 1; winD < 0 && d <= maxD; d++) {
    // The diagonals a path of d edits can sit on inside the two texts.
    let kLo = Math.max(-d, d - 2 * m);
    const kHi = Math.min(d, 2 * n - d);
    if (((kLo + d) & 1) !== 0) kLo++;
    const pBase = bandBase[d - 1];
    const pLo = bandLo[d - 1];
    const pHi = pLo + 2 * (bandLen - pBase - 1);
    if (kLo > kHi) {
      // No diagonal is available at this d; an empty band reads as all-unreached.
      bandBase.push(bandLen);
      bandLo.push(kLo);
      continue;
    }
    const count = (kHi - kLo) / 2 + 1;
    ensure(bandLen + count);
    const base = bandLen;
    bandBase.push(base);
    bandLo.push(kLo);
    // The read slot of this band's deletion predecessor, walked with k.
    let rSlot = pBase + (kLo - 1 - pLo) / 2;
    let slot = base;
    for (let k = kLo; k <= kHi; k += 2, slot++, rSlot++) {
      // The deletion's path sits on diagonal k-1, the insertion's on k+1, both
      // in the previous band (outside it, no path reaches).
      const remOld = k - 1 >= pLo && k - 1 <= pHi ? bandX[rSlot] : UNREACH;
      const addOld = k + 1 >= pLo && k + 1 <= pHi ? bandX[rSlot + 1] : UNREACH;
      const canDel = remOld !== UNREACH && remOld + 1 < n;
      const canIns = addOld !== UNREACH && addOld - k < m;
      if (!canDel && !canIns) {
        bandX[slot] = UNREACH;
        bandStep[slot] = 0;
        continue;
      }
      // Furthest into the old text wins; on an equal reach, the deletion's.
      const byDel = canDel ? remOld + 1 : -2;
      const byIns = canIns ? addOld : -2;
      let nx;
      let step;
      if (byDel >= byIns) {
        nx = remOld + 1;
        step = 1;
      } else {
        nx = addOld;
        step = 0;
      }
      // Follow the snake of lines equal in both texts as far as it goes.
      let ny = nx - k;
      while (nx + 1 < n && ny + 1 < m && a[nx + 1] === b[ny + 1]) {
        nx++;
        ny++;
      }
      bandX[slot] = nx;
      bandStep[slot] = step;
      if (nx + 1 >= n && ny + 1 >= m) {
        winD = d;
        winK = k;
        bandLen = slot + 1;
        break;
      }
    }
    if (winD < 0) bandLen = base + count;
  }
  if (winD < 0) throw new Error('makefun-diff: the search ended without reaching both ends');

  // Read the winning path back: from its last state to the first, each state
  // contributes its snake (kept lines) and the single edit step that made it.
  // Segments are collected in reverse, then replayed forward with merging.
  const rev = [];
  let k = winK;
  for (let d = winD; d >= 1; d--) {
    const slot = bandBase[d] + (k - bandLo[d]) / 2;
    const stateX = bandX[slot];
    const step = bandStep[slot];
    const pk = step === 1 ? k - 1 : k + 1;
    const prevX = bandX[bandBase[d - 1] + (pk - bandLo[d - 1]) / 2];
    const snake = stateX - (prevX + (step === 1 ? 1 : 0));
    if (snake > 0) rev.push(KEEP, snake);
    rev.push(step === 1 ? DEL : INS, 1);
    k = pk;
  }
  const startX = bandX[0];
  if (startX + 1 > 0) rev.push(KEEP, startX + 1);
  for (let i = rev.length - 2; i >= 0; i -= 2) {
    const kind = rev[i];
    const count = rev[i + 1];
    const last = seg.length - 2;
    if (last >= 0 && seg[last] === kind) seg[last + 1] += count;
    else seg.push(kind, count);
  }
}

/** The patch for one case's input { old, new }, exactly as the rule writes it. */
export function run(input) {
  if (input === null || typeof input !== 'object' || typeof input.old !== 'string' || typeof input.new !== 'string') {
    throw new TypeError('makefun-diff: the input is { old, new }, two strings');
  }
  const aLines = splitLines(input.old);
  const bLines = splitLines(input.new);
  const n = aLines.length;
  const m = bLines.length;

  // Intern every distinct line of the pair to an integer id.
  const ids = new Map();
  let nextId = 0;
  const intern = (lines) => {
    const out = new Uint32Array(lines.length);
    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      let id = ids.get(line);
      if (id === undefined) {
        id = nextId++;
        ids.set(line, id);
      }
      out[i] = id;
    }
    return out;
  };
  const a = intern(aLines);
  const b = intern(bLines);

  // The common prefix of lines, then the common suffix of the lines left.
  let prefix = 0;
  while (prefix < n && prefix < m && a[prefix] === b[prefix]) prefix++;
  let suffix = 0;
  while (suffix < n - prefix && suffix < m - prefix && a[n - 1 - suffix] === b[m - 1 - suffix]) suffix++;

  // The whole edit script as flat [kind, count] segments.
  const seg = [];
  const addSeg = (kind, count) => {
    if (count <= 0) return;
    const last = seg.length - 2;
    if (last >= 0 && seg[last] === kind) seg[last + 1] += count;
    else seg.push(kind, count);
  };
  addSeg(KEEP, prefix);
  if (prefix + suffix < n || prefix + suffix < m) {
    searchMiddle(
      a.subarray(prefix, n - suffix),
      n - suffix - prefix,
      b.subarray(prefix, m - suffix),
      m - suffix - prefix,
      seg,
    );
  }
  addSeg(KEEP, suffix);

  // Group the script into change runs: a maximal stretch of deletions and
  // insertions between kept lines, at old line o and new line p.
  const changes = [];
  let o = 0;
  let p = 0;
  let deleted = 0;
  let inserted = 0;
  let open = null;
  for (let i = 0; i < seg.length; i += 2) {
    const kind = seg[i];
    const count = seg[i + 1];
    if (kind === KEEP) {
      o += count;
      p += count;
      open = null;
      continue;
    }
    if (open === null) {
      open = { o, p, dels: 0, ins: 0 };
      changes.push(open);
    }
    if (kind === DEL) {
      open.dels += count;
      o += count;
      deleted += count;
    } else {
      open.ins += count;
      p += count;
      inserted += count;
    }
  }

  // Group change runs into hunks: runs at most 2*CONTEXT kept lines apart
  // share a hunk.
  const hunks = [];
  for (const c of changes) {
    const h = hunks[hunks.length - 1];
    const prevChange = h === undefined ? undefined : h[h.length - 1];
    if (prevChange !== undefined && c.o - (prevChange.o + prevChange.dels) <= 2 * CONTEXT) h.push(c);
    else hunks.push([c]);
  }

  // Write the patch. Line pieces go into one array, joined once at the end; a
  // line with no trailing newline is written with one and followed by "%".
  const out = [`makefun-diff/1 old=${n} new=${m} hunks=${hunks.length} deleted=${deleted} inserted=${inserted}\n`];
  const emit = (op, line) => {
    if (line.endsWith('\n')) out.push(op, line);
    else out.push(op, line, '\n%\n');
  };
  for (const h of hunks) {
    const first = h[0];
    const lastChange = h[h.length - 1];
    const oldStart = Math.max(0, first.o - CONTEXT);
    const newStart = first.p - (first.o - oldStart);
    const after = Math.min(CONTEXT, n - (lastChange.o + lastChange.dels));
    const oldEnd = lastChange.o + lastChange.dels + after;
    const newEnd = lastChange.p + lastChange.ins + after;
    out.push(`@ ${oldStart + 1} ${oldEnd - oldStart} ${newStart + 1} ${newEnd - newStart}\n`);
    let at = oldStart;
    for (const c of h) {
      for (; at < c.o; at++) emit('=', aLines[at]);
      for (let i = 0; i < c.dels; i++) emit('-', aLines[c.o + i]);
      for (let i = 0; i < c.ins; i++) emit('+', bLines[c.p + i]);
      at = c.o + c.dels;
    }
    for (; at < oldEnd; at++) emit('=', aLines[at]);
  }
  return out.join('');
}
