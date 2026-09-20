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
bend src/negharm.bend --check-only
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

### Milestone 2 — Dominant 7ths, tritone substitution, inversion, negative harmony: done, all laws proved

`src/chord.bend` (dom7, tritone sub, inversion), `src/negharm.bend`
(negative harmony).

**Model.** `dom7(root)` is `Chord{root, [0, 4, 7, 10]}` (root, major 3rd,
perfect 5th, minor 7th). Its tritone substitute is just `Chord.transpose(6,
_)`, reusing Milestone 1's transpose — the substitute keeps the same shape
(interval list) and moves the root a tritone (6 half steps) away, which is
exactly what a chord transposition already means in this model.

Chord *inversion* moves the bottom interval to the top: the interval list
rotates left by one (an octave move is invisible to a pitch-class-only
model, so "move the bottom note up an octave" is just "move it to the end
of the list"). Proving that `n` inversions of an `n`-note chord return the
original needed a small append/rotation library (`append`, `rotate1`,
`rotate_iter` in `chord.bend`) and, in `PROOF.bend`, the standard textbook
argument: rotating `append(t, ys)` left by `len(t)` lands on `append(ys,
t)` (`rotate_append`, by induction on `t` using `append_assoc` and
`append_nil_r`); setting `ys = []` gives `rotate_iter(len(xs), xs) == xs`
directly. Interval lists are declared `+List<Nat>` (`List<&2, Nat>`,
Base's "Data-kinded, freely copiable" list) because the proof needs to
reuse the same list at several points (e.g. `ys` and `append(ys, [h])`);
plain `List<Nat>` defaults to affine (`List<&1, Nat>`, used-once) and the
checker rejects a second use with a precise "consumed more than once"
error, which is what drove this choice.

Negative harmony reflects pitch classes around an axis tied to a tonic. It
is built from one fixed reflection, `mirror` (a 12-case table, the
reflection around C: `C` stays `C`, `Db`/`B` swap, and so on; `Gb`,
directly opposite `C`, stays put), conjugated by a transpose so it reflects
around any tonic: shift the wheel so `tonic` sits where `C` sits, `mirror`,
shift back. (Some treatments of negative harmony place the axis at the
midpoint between a tonic and its fifth rather than at the tonic itself —
that's a different, half-step-shifted `mirror` table; the involution proof
goes through identically.) `comp(n)`, `n`'s complement to a full turn
(`index(n) + comp(n) == 12`, checkable per case since both sides are
literals), is what lets the "shift, mirror, shift back, shift, mirror,
shift back" chain collapse: each pair of opposing shifts is a shift by 12,
which `transpose_period12` (12 concrete cases, since `succ` only reduces on
a known note) erases, leaving `mirror(mirror(n)) == n`.

**Laws proved** (`LAWS.bend`, proofs in `PROOF.bend`):

- `tritone_sub_guide_tones`: for every X7, its 3rd and 7th match, as pitch
  classes, the 7th and 3rd of its tritone substitute. (One direction lands
  on the identical interval directly — `6 + 4 == 10` — the other needs
  `transpose_add12`, since `6 + 10 == 16 == 12 + 4`.)
- `invert_n_identity`: inverting an `n`-note chord `n` times returns the
  original chord.
- `negative_harmony_involution`: applying negative harmony twice, around
  the same tonic, is the identity. Proved by case-splitting the tonic into
  its 12 concrete notes (so `index`/`comp` reduce to literals) and calling
  one shared lemma, `neg_involution_core`, per case.

Run `bend PROOF.bend` from the repo root to check all six laws (three from
Milestone 1, three from Milestone 2).

### Milestones 3-5

Not started yet: guitar voicings (3), voice leading (4), the
exercise-generator CLI (5).

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

- `List<A>` (no quantity prefix) defaults to `List<&1, A>` (affine, used
  once) regardless of whether `A` itself is `Data`; to get a freely
  copiable list you must write `+List<A>` (`List<&2, A>`) explicitly, and
  every function signature touching that list has to agree on the
  quantity — a plain `List<Nat>` parameter rejects a `List<&2, Nat>`
  argument outright (`expected: List<&1, Nat>`, `observed: List<&2,
  Nat>`). This is documented (`bend guide`'s Kinds section) but only
  becomes visible once a proof actually needs to reuse a list, which is
  why Milestone 1's interval lists could stay plain `List<Nat>` while
  Milestone 2's inversion proof needed `+List<Nat>` throughout
  `chord.bend`.

No compiler crashes or incomprehensible errors were hit in Milestones 1-2;
no GitHub issue filed yet.
