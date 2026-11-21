# Sokoban Solver

A push-optimal Sokoban solver, built for the make.fun bounty
`sokoban-solver-01-run-20261121` — "Build the best Sokoban solver, 21 November 2026".

## What it does

`main.ts` (Node 22, zero dependencies) reads the five instances of a set
from `/input/i001..i005/level.txt` (XSB) and writes each answer to
`/output/<id>/solution.txt` — the player's moves in LURD, in as few pushes
as possible. The whole set is answered in one run, well inside the 60-second
budget, and two runs write byte-identical output.

## How it works

Every generated level is a hallway with one to four independent rooms off it,
and a box pushed out of a room can never be pushed back, so a level's
push-optimal count is the sum of its rooms' optima. The solver therefore:

1. **Splits the level into rooms** — it cuts the hallway's dead squares out
   of the floor and flood-fills the rest; each part holding boxes is a room.
2. **Solves each room push-optimally with A\* over pushes.** A state is the
   boxes' squares plus the player's reachable region; one push costs 1. The
   heuristic is the minimum assignment of boxes to distinct goals under
   wall-only push distances, which never overestimates the pushes still
   needed, so the first solved state popped is push-optimal.
3. **Prunes dead states soundly** — boxes on dead squares (no pull sequence
   from any goal reaches them) and frozen boxes off their goals (a greatest
   fixed-point freeze test: a box no push can ever move).
4. **Joins the rooms** — the player's walks between rooms are shortest-path
   BFS walks; other rooms' boxes stand as walls while a room is solved.

Fallbacks, in order, are a plain push BFS per room, a push A\* over the whole
level, and a move-space A\* as a last resort, so an awkward level still gets
a solving answer instead of an empty one. All budgets are fixed counts of
work, never the clock, and tie-breaking is by fixed direction order and
insertion order, so the program is fully deterministic.

## Local check

From the competition kit directory:

```
node cli/makefun.mjs grade-local --kit . --bot <this directory> --driver process
```

## Referral

make.fun referral code: `4s3d9qw1`

## License

MIT — see `LICENSE`.
