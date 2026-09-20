# Bending: a jazz theory engine in Bend 2

A jazz-theory engine written in [Bend 2](https://github.com/bendlang/bend), a
language with dependent types and machine-checked proofs. Every milestone
states its laws in `LAWS.bend` and proves them in `PROOF.bend`; `bend
PROOF.bend` is the gate, and it must print `All terms check.` before a
milestone is considered done.

## Toolchain

Bend 2 (`bend2/main.ts` in `bendlang/bend`) is a TypeScript program run with
`bun`. There is no published binary release used here; this repo assumes a
`bend` command on `PATH` that runs `bun <path-to-bendlang/bend>/bend2/main.ts
"$@"`. Everything below was developed and checked against the JavaScript
target (the default for `bend file.bend`, no `-o`), which is fast enough to
iterate against; nothing here has been compiled to a native binary.

```
bend PROOF.bend          # the gate: must print "All terms check."
bend src/note.bend --check-only
bend src/chord.bend --check-only
```

## Status by milestone

### Milestone 1 — Pitch classes: done, all laws proved

`src/note.bend`, `src/chord.bend`.

**Model.** Base (Bend's standard library) has no generic `Fin(n)` type, so a
pitch class (`Note`) is modeled as a closed, 12-constructor enum (`C, Db, D,
..., B`) — the concrete stand-in for `Fin(12)` the task asked for. This
choice matters for the proofs: it lets transposition be defined as *iterated
succession* (`transpose(i, n)` applies `succ`, the "next note up a half
step, wrapping B to C" function, `i` times) rather than as arithmetic through
`Nat.mod`. Base ships `Nat.mod` (via `Nat.divmod`, a fuelled/countdown
recursion), but no lemmas about it — proving things like `(a+b) mod 12 ==
((a mod 12)+(b mod 12)) mod 12` from scratch, against that specific
implementation, would have been a substantial side project in its own right,
disproportionate to what a pitch-class model needs. With transposition as
iterated `succ`, `transpose(a+b, n) == transpose(b, transpose(a, n))` is a
one-line structural induction on `a` — see `PROOF.bend`.

A chord (`Chord`) is a root pitch class plus a list of intervals (half steps
above the root, as `Nat`). Its notes are read off by transposing the root by
each interval. Transposing a chord only ever moves its root; the interval
list — the chord's "shape" — never changes.

**Laws proved** (`LAWS.bend`, proofs in `PROOF.bend`):

- `transpose_add`: transposing by `a` then by `b` is the same as
  transposing by `a+b` in one step.
- `transpose_zero`: transposing by 0 is the identity.
- `transpose_preserves_intervals`: transposing a chord (moving only its
  root) gives the same notes as transposing every note of the chord
  individually — i.e. transposition never changes a chord's interval set,
  only where it sits. This needed two helper lemmas proved along the way,
  `add_comm` for Base's `Nat.add` (Base states `Nat.add` but proves no
  algebra about it) and `transpose_comm` (transposing by `h` then `k` is the
  same note as `k` then `h`), both in `PROOF.bend`.

Run `bend PROOF.bend` from the repo root to check all three.

### Milestones 2-5

Not started yet. Per the task, Milestone 1 stops here for review of the
model before continuing to chords/tritone substitution (2), guitar voicings
(3), voice leading (4) and the exercise-generator CLI (5).

## Known compiler friction (not a Bend issue report yet)

- Recursive proof `def`s must list the argument that structurally shrinks
  *first*; Bend's termination checker reads a recursive call's arguments
  left to right and requires everything before the shrinking one to be
  passed unchanged. This is documented (`bend guide` says "put the
  parameter that shrinks first") but easy to trip over when a law's most
  natural `for` order doesn't put the inductive parameter first — e.g.
  `transpose(i, n)` (amount before note) and `transpose_add(a, b, n)`
  (the induction variable `a` before the pitch class) read a little
  differently from the "note, then how far" phrasing a jazz musician would
  use.
- `+` (reusable) quantity annotations are required on any `Data`-kinded
  binder used more than once in a body, including inside a pattern match
  (`case +h <> r:`) — Bend's checker reports these precisely
  (`expected: b`, `observed: b (consumed more than once)`), so this was
  mechanical to fix, not a design problem.

No compiler crashes or incomprehensible errors were hit in Milestone 1; no
GitHub issue filed yet.
