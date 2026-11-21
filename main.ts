// Sokoban solver for make.fun's sokoban-solver-01-run-20261121.
//
// Strategy: every generated level is a hallway with 1-4 independent rooms off
// it, and a box pushed out of a room can never come back, so a level's
// push-optimal count is the sum of its rooms' optima. This program splits a
// level into its rooms and solves each room push-optimally, then joins the
// rooms' move strings with the player's walks between them.
//
// Each room is solved with A* over pushes (not single steps): a state is the
// boxes' squares plus the player's reachable region, a push costs 1, and the
// heuristic is the minimum assignment of the boxes to distinct goals under
// wall-only push distances, which never overestimates the pushes still
// needed, so the first solved state popped is push-optimal. Dead states are
// pruned with two sound tests: a box on a dead square (no sequence of pulls
// from any goal reaches it) and a frozen box off its goal (a greatest
// fixed-point freeze test: a box that no push can ever move, because every
// push direction is blocked by a wall or another box that can never move).
//
// Everything is budgeted by work, never by the clock: expansion caps are
// fixed counts, tie-breaking is by fixed direction order and insertion
// order, so two runs write byte-identical output. Fallbacks, in order, are
// a plain push BFS per room, a push A* over the whole level, and a
// move-space A* (fewest moves, not fewest pushes) as a last resort so an
// awkward level still gets a solving answer instead of an empty one.
//
// Node 22, no dependencies, no network, no clock reads.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Work budgets (state expansions), never the clock.
const ASTAR_CAP = 200_000;
const BFS_CAP = 400_000;
const WHOLE_CAP = 150_000;
const MOVE_CAP = 150_000;

const DIRS = [
  [0, -1, 'u', 'U'],
  [0, 1, 'd', 'D'],
  [-1, 0, 'l', 'L'],
  [1, 0, 'r', 'R'],
];
const OFFS = (w) => [-w, w, -1, 1];

/** Parse XSB text (# wall, space floor, . goal, $ box, * box on goal, @ player, + player on goal). */
function parseLevel(text) {
  const rows = text.split('\n').filter((r) => r.length > 0);
  const h = rows.length;
  const w = Math.max(...rows.map((r) => r.length));
  const wall = new Uint8Array(w * h).fill(1);
  const goals = [];
  const boxes = [];
  let player = -1;
  rows.forEach((row, y) => {
    for (let x = 0; x < row.length; x++) {
      const ch = row[x];
      const i = y * w + x;
      if (ch === '#') continue;
      wall[i] = 0;
      if (ch === '.' || ch === '*' || ch === '+') goals.push(i);
      if (ch === '$' || ch === '*') boxes.push(i);
      if (ch === '@' || ch === '+') player = i;
    }
  });
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      if (x === 0 || y === 0 || x === w - 1 || y === h - 1) wall[y * w + x] = 1;
    }
  }
  return { w, h, wall, goals, boxes: boxes.sort((a, b) => a - b), player };
}

/** Squares a box can be pulled back to some goal from, ignoring other boxes. */
function liveSquares(level) {
  const { w, wall, goals } = level;
  const size = wall.length;
  const live = new Uint8Array(size);
  const queue = [...goals];
  for (const g of goals) live[g] = 1;
  for (let qi = 0; qi < queue.length; qi++) {
    const x = queue[qi];
    for (let k = 0; k < 4; k++) {
      const d = OFFS(w)[k];
      const y = x - d;
      if (y < 0 || y >= size || wall[y]) continue;
      const behind = y - d;
      if (behind < 0 || behind >= size || wall[behind]) continue;
      if (!live[y]) {
        live[y] = 1;
        queue.push(y);
      }
    }
  }
  return live;
}

/** Minimum pushes to bring one box from any square to `goalSq`, walls only (player reachability relaxed). */
function pushDist(goalSq, wall, w, size) {
  const dist = new Int32Array(size).fill(-1);
  dist[goalSq] = 0;
  const queue = [goalSq];
  for (let qi = 0; qi < queue.length; qi++) {
    const y = queue[qi];
    for (let k = 0; k < 4; k++) {
      const d = OFFS(w)[k];
      const x = y - d;
      if (x < 0 || x >= size || wall[x]) continue;
      const behind = x - d;
      if (behind < 0 || behind >= size || wall[behind]) continue;
      if (dist[x] !== -1) continue;
      dist[x] = dist[y] + 1;
      queue.push(x);
    }
  }
  return dist;
}

/** All permutations of 0..n-1 in fixed lexicographic order. */
function permutations(n) {
  const out = [];
  const cur = [];
  const used = new Array(n).fill(false);
  const rec = () => {
    if (cur.length === n) {
      out.push(cur.slice());
      return;
    }
    for (let i = 0; i < n; i++) {
      if (used[i]) continue;
      used[i] = true;
      cur.push(i);
      rec();
      cur.pop();
      used[i] = false;
    }
  };
  rec();
  return out;
}

/**
 * Admissible push heuristic: the cheapest assignment of boxes to distinct
 * goals under the wall-only push distances (exact assignment for up to 5
 * boxes, sum of per-box minima beyond that). Infinity when no assignment
 * exists, which proves the state unsolvable.
 */
function makeHeuristic(boxes0, distG) {
  const n = boxes0.length;
  if (n <= 5) {
    const perms = permutations(n);
    return (boxes) => {
      let best = Infinity;
      for (const p of perms) {
        let s = 0;
        let ok = true;
        for (let i = 0; i < n; i++) {
          const d = distG[p[i]][boxes[i]];
          if (d < 0) {
            ok = false;
            break;
          }
          s += d;
        }
        if (ok && s < best) best = s;
      }
      return best;
    };
  }
  return (boxes) => {
    let s = 0;
    for (const b of boxes) {
      let m = Infinity;
      for (const dg of distG) if (dg[b] >= 0 && dg[b] < m) m = dg[b];
      if (m === Infinity) return Infinity;
      s += m;
    }
    return s;
  };
}

/**
 * Whether some box off its goal can never move again: the greatest set F of
 * boxes such that every box in F has all four push directions blocked by a
 * wall or another box of F. Boxes outside F have a push direction open once
 * F is treated as walls, so they are not frozen; a box in F can never be the
 * first of F to move, so it can never move at all.
 */
function frozenOffGoal(boxes, wall, goal, w) {
  const frozen = new Set(boxes);
  let changed = true;
  while (changed) {
    changed = false;
    for (const b of [...frozen]) {
      let canMove = false;
      for (let k = 0; k < 4; k++) {
        const d = OFFS(w)[k];
        const dest = b + d;
        const behind = b - d;
        if (!wall[dest] && !frozen.has(dest) && !wall[behind] && !frozen.has(behind)) {
          canMove = true;
          break;
        }
      }
      if (canMove) {
        frozen.delete(b);
        changed = true;
      }
    }
  }
  for (const b of frozen) if (!goal[b]) return true;
  return false;
}

/** Flood-fill the player's region from `from` around walls and `occ` boxes; returns its lowest square. */
function regionLow(level, occ, from, seen, stamp, stack) {
  const { w, wall } = level;
  const size = wall.length;
  let low = from;
  let n = 0;
  stack[n++] = from;
  seen[from] = stamp;
  while (n > 0) {
    const p = stack[--n];
    if (p < low) low = p;
    for (let k = 0; k < 4; k++) {
      const q = p + OFFS(w)[k];
      if (q < 0 || q >= size) continue;
      if (!wall[q] && !occ[q] && seen[q] !== stamp) {
        seen[q] = stamp;
        stack[n++] = q;
      }
    }
  }
  return low;
}

/** Shortest walk from `from` to `to` around walls and boxes, lower-case LURD (first direction first on ties). */
function walkTo(level, occ, from, to) {
  const { w, wall } = level;
  const size = wall.length;
  if (from === to) return '';
  const prev = new Int32Array(size).fill(-1);
  const how = new Array(size);
  const queue = [from];
  prev[from] = from;
  for (let qi = 0; qi < queue.length; qi++) {
    const p = queue[qi];
    if (p === to) break;
    for (let k = 0; k < 4; k++) {
      const q = p + OFFS(w)[k];
      if (q < 0 || q >= size) continue;
      if (wall[q] || occ[q] || prev[q] !== -1) continue;
      prev[q] = p;
      how[q] = DIRS[k][2];
      queue.push(q);
    }
  }
  if (prev[to] === -1) throw new Error('walkTo: push square out of reach');
  let s = '';
  for (let p = to; p !== from; p = prev[p]) s = how[p] + s;
  return s;
}

/** The player's square after playing `moves` (case aside) from `from`. */
function endOf(w, from, moves) {
  let p = from;
  for (const ch of moves.toLowerCase()) p += ch === 'u' ? -w : ch === 'd' ? w : ch === 'l' ? -1 : 1;
  return p;
}

/** A binary heap on [f, h, seq, index, g], ties by lower h then earlier insertion. */
function makeHeap() {
  const heap = [];
  const less = (a, b) => a[0] < b[0] || (a[0] === b[0] && (a[1] < b[1] || (a[1] === b[1] && a[2] < b[2])));
  return {
    get size() {
      return heap.length;
    },
    push(e) {
      let i = heap.length;
      heap.push(e);
      while (i > 0) {
        const p = (i - 1) >> 1;
        if (!less(heap[i], heap[p])) break;
        [heap[i], heap[p]] = [heap[p], heap[i]];
        i = p;
      }
    },
    pop() {
      const top = heap[0];
      const last = heap.pop();
      if (heap.length > 0) {
        heap[0] = last;
        for (let i = 0; ; ) {
          let c = 2 * i + 1;
          if (c >= heap.length) break;
          if (c + 1 < heap.length && less(heap[c + 1], heap[c])) c++;
          if (!less(heap[c], heap[i])) break;
          [heap[i], heap[c]] = [heap[c], heap[i]];
          i = c;
        }
      }
      return top;
    },
  };
}

/**
 * Push-optimal solution of `level` ({pushes, moves}) or null when the search
 * gives up. A* when `useH` (admissible assignment heuristic), plain push BFS
 * otherwise; both prune dead squares and frozen boxes, and both keep a
 * transposition table keyed by the boxes plus the player's region.
 */
function solvePush(level, maxExpansions, useH) {
  const { w, wall, goals, boxes: startBoxes, player: startPlayer } = level;
  const size = wall.length;
  const goal = new Uint8Array(size);
  for (const g of goals) goal[g] = 1;
  const live = liveSquares(level);
  if (startBoxes.some((b) => !live[b])) return null;
  const solved = (bs) => bs.every((b) => goal[b]);
  if (solved(startBoxes)) return { pushes: 0, moves: '' };
  const distG = goals.map((g) => pushDist(g, wall, w, size));
  const heur = useH ? makeHeuristic(startBoxes, distG) : () => 0;
  const numericKey = startBoxes.length <= 5;
  const keyOf = (bs, low) => {
    if (!numericKey) return `${low}|${bs.join(',')}`;
    let k = low;
    for (const b of bs) k = k * size + b;
    return k;
  };

  const seen = new Int32Array(size);
  const seen2 = new Int32Array(size);
  const occ = new Uint8Array(size);
  const occ2 = new Uint8Array(size);
  const stack = new Int32Array(size);
  const stack2 = new Int32Array(size);
  let stamp = 0;
  let stamp2 = 0;
  // The region's lowest square from `from`, over `boxes`: its own stamp and
  // occupancy arrays, so it never disturbs the expansion loop's state.
  const region = (boxes, from) => {
    for (const b of boxes) occ2[b] = 1;
    const low = regionLow(level, occ2, from, seen2, ++stamp2, stack2);
    for (const b of boxes) occ2[b] = 0;
    return low;
  };

  const stBoxes = [startBoxes.slice()];
  const stPlayer = [startPlayer];
  const stG = [0];
  const parent = [-1];
  const pFrom = [0];
  const pTo = [0];
  const pDir = [0];
  const best = new Map();
  const h0 = heur(startBoxes);
  if (h0 === Infinity) return null;
  best.set(keyOf(startBoxes, region(startBoxes, startPlayer)), 0);
  const heap = makeHeap();
  let seq = 0;
  heap.push([h0, h0, seq++, 0, 0]);
  let expanded = 0;
  let found = -1;
  while (heap.size > 0) {
    const [, , , s, g] = heap.pop();
    if (stG[s] !== g) continue; // stale entry: a cheaper path to this state was found
    const boxes = stBoxes[s];
    if (solved(boxes)) {
      found = s;
      break;
    }
    if (expanded >= maxExpansions) return null;
    expanded++;
    const player = stPlayer[s];
    for (const b of boxes) occ[b] = 1;
    regionLow(level, occ, player, seen, ++stamp, stack);
    const here = stamp;
    for (let bi = 0; bi < boxes.length; bi++) {
      const b = boxes[bi];
      for (let k = 0; k < 4; k++) {
        const d = OFFS(w)[k];
        const behind = b - d;
        const target = b + d;
        if (behind < 0 || behind >= size || target < 0 || target >= size) continue;
        if (seen[behind] !== here || wall[target] || occ[target] || !live[target]) continue;
        occ[b] = 0;
        occ[target] = 1;
        const next = boxes.slice();
        next[bi] = target;
        next.sort((x, y) => x - y);
        const frozen = frozenOffGoal(next, wall, goal, w);
        let key = -1;
        if (!frozen) key = keyOf(next, region(next, b));
        occ[target] = 0;
        occ[b] = 1;
        if (frozen) continue;
        const prevG = best.get(key);
        if (prevG !== undefined && prevG <= g + 1) continue;
        const h = heur(next);
        if (h === Infinity) continue;
        best.set(key, g + 1);
        const t = stBoxes.length;
        stBoxes.push(next);
        stPlayer.push(b);
        stG.push(g + 1);
        parent.push(s);
        pFrom.push(b);
        pTo.push(target);
        pDir.push(k);
        heap.push([g + 1 + h, h, seq++, t, g + 1]);
      }
    }
    for (const b of boxes) occ[b] = 0;
  }
  if (found < 0) return null;
  // Rebuild the moves: walk to each push's square, then push.
  const path = [];
  for (let s = found; s > 0; s = parent[s]) path.push(s);
  path.reverse();
  let moves = '';
  let player = startPlayer;
  let boxes = startBoxes.slice();
  for (const s of path) {
    const from = pFrom[s];
    const to = pTo[s];
    const k = pDir[s];
    const d = OFFS(w)[k];
    for (const b of boxes) occ[b] = 1;
    moves += walkTo(level, occ, player, from - d);
    for (const b of boxes) occ[b] = 0;
    moves += DIRS[k][3];
    player = from;
    boxes = stBoxes[s].slice();
  }
  return { pushes: path.length, moves };
}

/**
 * The level's rooms: cut the dead squares of the player's row (the hallway:
 * a box there reaches no goal) out of the floor; each remaining part holding
 * a box is a room. Null when a box starts in the hallway, a goal falls
 * outside every part, or some part's boxes and goals do not match.
 */
function roomsOf(level) {
  const { w, wall, goals, boxes, player } = level;
  const size = wall.length;
  const live = liveSquares(level);
  const row = Math.floor(player / w);
  const cut = new Uint8Array(size);
  for (let i = row * w; i < (row + 1) * w; i++) if (!wall[i] && !live[i]) cut[i] = 1;
  if (boxes.some((b) => cut[b])) return null;
  const part = new Int32Array(size).fill(-1);
  const rooms = [];
  for (let s = 0; s < size; s++) {
    if (wall[s] || cut[s] || part[s] >= 0) continue;
    const squares = [s];
    part[s] = rooms.length;
    for (let i = 0; i < squares.length; i++) {
      for (let k = 0; k < 4; k++) {
        const q = squares[i] + OFFS(w)[k];
        if (q < 0 || q >= size) continue;
        if (!wall[q] && !cut[q] && part[q] < 0) {
          part[q] = rooms.length;
          squares.push(q);
        }
      }
    }
    rooms.push({ squares, boxes: [], goals: [], done: false });
  }
  for (const b of boxes) rooms[part[b]].boxes.push(b);
  for (const g of goals) if (part[g] >= 0) rooms[part[g]].goals.push(g);
  if (goals.some((g) => part[g] < 0)) return null;
  if (rooms.some((r) => r.boxes.length !== r.goals.length)) return null;
  return rooms.filter((r) => r.boxes.length > 0);
}

/**
 * Solve room by room: each room's push-optimal solution in turn, the other
 * rooms' boxes standing as walls (on their goals once their room is done),
 * the player walking on from where the last room left it. Null when a room
 * gives up.
 */
function solveByRooms(level) {
  const rooms = roomsOf(level);
  if (rooms === null) return null;
  let player = level.player;
  let pushes = 0;
  let moves = '';
  for (const room of rooms) {
    const wall = level.wall.slice();
    for (const other of rooms) {
      if (other === room) continue;
      for (const b of other.done ? other.goals : other.boxes) wall[b] = 1;
    }
    const sub = {
      w: level.w,
      h: level.h,
      wall,
      goals: room.goals.slice().sort((a, b) => a - b),
      boxes: room.boxes.slice().sort((a, b) => a - b),
      player,
    };
    let sol = solvePush(sub, ASTAR_CAP, true);
    if (sol === null) sol = solvePush(sub, BFS_CAP, false);
    if (sol === null) return null;
    pushes += sol.pushes;
    moves += sol.moves;
    player = endOf(level.w, player, sol.moves);
    room.done = true;
  }
  return { pushes, moves };
}

/** Last resort: plain move-space A* (fewest moves), the baseline's shape, written fresh. */
function solveMoves(level, maxExpansions) {
  const { w, wall, goals, boxes: startBoxes, player: startPlayer } = level;
  const size = wall.length;
  const goal = new Uint8Array(size);
  for (const g of goals) goal[g] = 1;
  const dist = (b) => {
    let m = Infinity;
    for (const g of goals) {
      const d = Math.abs((g % w) - (b % w)) + Math.abs(Math.floor(g / w) - Math.floor(b / w));
      if (d < m) m = d;
    }
    return m;
  };
  const est = (bs) => bs.reduce((a, b) => a + dist(b), 0);
  const key = (p, bs) => `${p}|${bs.join(',')}`;
  const solved = (bs) => bs.every((b) => goal[b]);
  if (solved(startBoxes)) return { pushes: 0, moves: '' };
  const sp = [startPlayer];
  const sb = [startBoxes.slice()];
  const sg = [0];
  const parent = [-1];
  const step = [''];
  const best = new Map([[key(startPlayer, startBoxes), 0]]);
  const heap = makeHeap();
  let seq = 0;
  heap.push([est(startBoxes), est(startBoxes), seq++, 0, 0]);
  let expanded = 0;
  let found = -1;
  while (heap.size > 0) {
    const [, , , s, g] = heap.pop();
    if (sg[s] !== g) continue;
    const bs = sb[s];
    if (solved(bs)) {
      found = s;
      break;
    }
    if (expanded >= maxExpansions) return null;
    expanded++;
    const p = sp[s];
    for (let k = 0; k < 4; k++) {
      const d = OFFS(w)[k];
      const q = p + d;
      if (q < 0 || q >= size || wall[q]) continue;
      let nb = bs;
      const at = bs.indexOf(q);
      if (at >= 0) {
        const t = q + d;
        if (t < 0 || t >= size || wall[t] || bs.includes(t)) continue;
        nb = bs.slice();
        nb[at] = t;
        nb.sort((a, b) => a - b);
      }
      const kk = key(q, nb);
      const seenG = best.get(kk);
      if (seenG !== undefined && seenG <= g + 1) continue;
      best.set(kk, g + 1);
      const t = sp.length;
      sp.push(q);
      sb.push(nb);
      sg.push(g + 1);
      parent.push(s);
      step.push(at >= 0 ? DIRS[k][3] : DIRS[k][2]);
      heap.push([g + 1 + est(nb), est(nb), seq++, t, g + 1]);
    }
  }
  if (found < 0) return null;
  let moves = '';
  let pushes = 0;
  for (let t = found; t > 0; t = parent[t]) {
    moves = step[t] + moves;
    if (step[t] === step[t].toUpperCase()) pushes++;
  }
  return { pushes, moves };
}

/** Solve one level: rooms first, then whole-level push search, then move search. */
function solveLevel(text) {
  const level = parseLevel(text);
  if (level.boxes.length === 0) return '';
  let sol = solveByRooms(level);
  if (sol === null) sol = solvePush(level, WHOLE_CAP, true);
  if (sol === null) sol = solveMoves(level, MOVE_CAP);
  return sol === null ? '' : sol.moves;
}

for (const id of readdirSync(INPUT_DIR).sort()) {
  const moves = solveLevel(readFileSync(join(INPUT_DIR, id, 'level.txt'), 'utf8'));
  mkdirSync(join(OUTPUT_DIR, id), { recursive: true });
  writeFileSync(join(OUTPUT_DIR, id, 'solution.txt'), `${moves}\n`);
}
