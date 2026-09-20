# Bending: a jazz theory engine in Bend 2

A jazz-theory engine written in [Bend 2](https://github.com/bendlang/bend), a
language with dependent types and machine-checked proofs. Every milestone
states its laws in `LAWS.bend` and proves them in `PROOF.bend`; `bend
PROOF.bend` is the gate, and it must print `All terms check.` before a
milestone is considered done.

All five milestones are implemented; **10 of the laws stated are proved**
(`bend PROOF.bend` → `All terms check.`). The one gap is noted where it
is, not smoothed over: `solve_parallel` (Milestone 4's divide-and-conquer
wrapper) is implemented and manually verified, reusing the sequential
`solve_chain` whose own boundedness law *is* proved, but its own
end-to-end proof needs two more lemmas not yet written — see Milestone
4 below for exactly what they'd need to show.

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
bend src/voicing.bend --check-only
bend src/voicelead.bend --check-only
bend src/exercise.bend --check-only
bend main.bend            # or: bend main.bend <key>, e.g. bend main.bend Bb
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

### Milestone 3 — Playable-by-construction guitar voicings: done, all laws proved

`src/voicing.bend` (fretboard model), `src/chord.bend` (drop-2/drop-3).

**Model.** Six strings, standard tuning low to high (E, A, D, G, B, E),
frets 0-15. A `Position` is `Muted{}` or `Fret{f}` (`f = 0` is an open
string). `Strings` is a plain 6-field record, one `Position` per string —
no array, since a guitar has a genuinely fixed 6 strings, not an arbitrary
`N`. `playable(strings)` computes, as a `Bool`, the three rules: every fret
`<= 15`; at most 4 strings are actually *pressed* (open and muted strings
need no finger, so `Fret{0}` and `Muted{}` don't count, simplifying away
barre chords, where one finger covers several strings at once); and the
highest and lowest *pressed* fret are at most 4 apart. `Voicing` pairs a
`Strings` with a proof that `playable(strings)` equals `True` — since that
proof's type is an equality between two concrete `Bool` computations, and
`Bool`'s two constructors are distinct, the type is uninhabited whenever
the strings genuinely aren't playable. Tried building one by hand with a
5-fret stretch (`x16000`) to confirm: `bend` rejects it at the `{==}` with
`expected: False{}`, `observed: True{}` — pointing at exactly the fret that
broke it. **No separate law is needed for "an unplayable Voicing cannot be
built" — the type is the proof.**

Drop-2 and drop-3 are defined over an ordered `List<Pc.Note>` (a chord's
notes stacked close, e.g. `[root, 3rd, 5th, 7th]`), not over a `Voicing`
directly: assigning an abstract note list onto specific strings and frets
is a search problem (which fret plays which note, given the tuning), left
for Milestones 4-5's voice-leading search. For a list of exactly 4 notes,
drop-2 moves the note at index 2 (2nd from the top) to the front and
drop-3 moves index 1 (3rd from the top) to the front — since a `Note` only
tracks pitch class, "drop an octave" is invisible here and both are just a
reordering. (Any other list length passes through unchanged: a total, if
musically unused, fallback.)

**Laws proved** (`LAWS.bend`, proofs in `PROOF.bend`):

- `drop2_is_permutation`, `drop3_is_permutation`: for every 4-note closed
  voicing, drop-2 (respectively drop-3) produces the same pitch classes,
  the same number of times each, as the original — formalized the same
  way `demos/proof_insertion_sort` formalizes "is a permutation of": equal
  `count(x, _)` for every pitch class `x`. Both follow from one lemma,
  `count_swap_adjacent` (swapping a list's first two elements doesn't
  change any element's count, via `bump_swap`, ported from that same
  demo), applied once (drop-3, a single adjacent swap) or twice (drop-2,
  two adjacent swaps compose to move the note two places).

Run `bend PROOF.bend` from the repo root to check all eight laws (three
from Milestone 1, three from Milestone 2, two from Milestone 3).

### Milestone 4 — Voice leading: core law proved; the parallel wrapper is implemented, not (yet) proved

`src/voicelead.bend`.

**Model.** `dist(x, y)` is circular pitch-class distance (0..6), built from
`Nat.sub`/`Nat.min`, no `Nat.mod` needed. `voices_bounded(xs, ys, n)` checks
every corresponding pair of two same-length note lists is within `n`
semitones; `chain_bounded(sol, anchor, n)` extends that down a whole list of
voicings, starting from a given anchor.

`solve_chain(chords, n, anchor)` walks a progression and, for each chord,
uses its closed/root-position voicing, failing (`None`) the moment that
voicing isn't within `n` of the previous one. **This was originally a
genuine search** over a chord's several inversions (`candidates`,
`Ch.invert_times`, still in the file), trying each until one was bounded,
then continuing with the rest of the progression. That algorithm hit a hard
Bend restriction: a function must be defined before its first use, and
mutual recursion is disallowed outright — but "try a candidate, and on
success continue processing the rest of the chords" is inherently two
phases that each call back into the other. Merging them into one function
(the guide's own suggested fix) using an eager-unconditional-both-branches
technique (borrowed from `demos/proof_insertion_sort`'s `dec`/`insert`,
which sidesteps a different instance of "can't match a computed value")
worked and typechecked, but made the resulting function's own correctness
proof (four mutually-recursive-shaped cases, each computing two candidate
continuations eagerly) look substantially harder than the single-candidate
version. Given "a law proved beats a feature," the search was descoped to
one fixed candidate per chord — weaker, but its boundedness law is a plain
structural induction on the chord list, fully proved below. Restoring a
real multi-candidate search *with* a proof is future work; the language
restriction that blocks the direct approach, and the merge technique that
gets around it, are worth knowing about either way.

`solve_parallel(chords, n, anchor)` is the divide-and-conquer version the
milestone asks for: split the progression in half, and run `solve_chain` on
each half via a parallel call (`left_res right_res = solve_chain(...)
solve_chain(...)`; call it as `solve_parallel!(...)` to run the split on
the GPU). Because `solve_chain` no longer searches, a chord's chosen
voicing never depends on the anchor it's approached from (only whether it's
*accepted* does) — so the right half's anchor (the closed voicing of the
left half's last chord) is computable directly from the chord list, with
no need to wait for the left half's own result. That is what makes the two
halves genuinely independent rather than one waiting on the other.
Implemented and manually verified (a 4-chord progression run through it
matches running it through `solve_chain` directly), but **its own
boundedness is not proved**: doing so needs two more lemmas beyond
`solve_chain`'s own (that `solve_chain`'s output multiset, restricted to
knowing only chord data, ends on the closed voicing of the progression's
last chord; and that `chain_bounded` composes across a list append) — each
roughly comparable in size to the proof already done for `solve_chain`, and
not completed here.

**Law proved** (`LAWS.bend`, proof in `PROOF.bend`):

- `solve_chain_bounded`: whenever `solve_chain` finds a solution, no voice
  in it ever moves more than `n` semitones between two consecutive chords
  (including the move from the given starting anchor into the first
  chord). The proof needed generic `Maybe` lemmas (`Some` is injective,
  `None ≠ Some`, both via the guide's constructor-discrimination-by-motive
  technique) since matching a computed value is disallowed and the search
  logic (`solve_chain_pick`) has to be its own function taking `Bool`/
  `Maybe` as plain parameters — see `PROOF.bend`.

### Milestone 5 — Exercise generator CLI: done, all laws proved

`src/exercise.bend`, `main.bend`.

**Model.** A guide-tone shell voicing plays just a chord's 3rd and 7th (the
two notes that define its quality) on the D and G strings, root and 5th
omitted — a standard, minimal jazz comping shape, and exactly the two notes
this milestone asks to mark. `guide_tone_shell` computes a fret for each
from the open string (`up_dist_note`, always 0..11) and picks whichever
octave placement of the second note keeps the pair's stretch small
(`nearest_fret`, choosing between that fret and the same pitch class 12
frets up if that's still ≤ 15). `min7_shell`/`dom7_shell`/`maj7_shell` wrap
this per quality, each **proving** playability by case-splitting the root
into its 12 concrete notes and closing every branch with `{==}` (the same
technique as Milestone 2's `transpose_period12`): a generic version sharing
one body across qualities was tried first, using Bend's `~` template
parameters for the interval numbers, but a template's body is still
typechecked once, abstractly, before any call site substitutes into it, so
its own `{==}` can't close — same obstacle as trying to match a computed
value, different context. Three short, repetitive 12-case functions instead
of one clever one, but each one's `{==}` is a real per-key check, not
assumed.

The ii-V-I chain (`ii_v_i_shells`) reuses the same recipe but lets each
chord after the first try to have *both* guide tones chase the *previous*
chord's fret on the same string (`nearest_fret` again, now against the
previous chord instead of against the chord's own other string), falling
back to the independent, always-safe placement whenever that would stretch
past 4 frets (`chord_step`). It also **swaps which string carries the 3rd
and which carries the 7th for V** relative to ii and I: ii's 3rd and V's
7th are the same or a near note, and ii's 7th resolves down a half step to
V's 3rd, but only if each keeps the string the other used. This is the
actual textbook reason shell voicings are famous for smooth voice leading;
without the swap, guide tones swapped strings mid-resolution and jumped
around (verified this made a real, measurable difference — see below).
Guaranteed playable by the same 12-way-match-then-`{==}` technique, now
chained: since the fret for V or I depends on the previous chord's fret,
which depends on the tonic, everything is still fully concrete once the
top-level match on `tonic` fixes it.

`main.bend` is the CLI: `bend main.bend <key>` (default `C` on a missing or
unrecognized key) prints the tonic and one line per chord — root, quality,
and each guide tone as `<string><fret>:<role>`. For example, `bend
main.bend F`:

```
key F
ii Gm7  D8:3 G10:7
V  C7  D8:7 G9:3
I  Fmaj7  D7:3 G9:7
```

Guide tones move by at most one fret between consecutive chords in every
key checked — before the ii/V/I string-swap fix, the same progression in C
moved by 6-7 frets per string between chords (verified with a scratch
script; not committed, since the point was the fix, not the broken
intermediate). Output is deliberately minimal and textual, per the
milestone's own instruction that Bend's string handling is slow: the
arithmetic happens in Bend, and anything prettier is left to a wrapper
outside it.

**Laws proved** (`LAWS.bend`, proof in `PROOF.bend`):

- `cycle_of_fourths_visits_all`: starting from any pitch class and
  repeatedly moving up a perfect 4th (5 half steps) visits each of the 12
  pitch classes exactly once (not zero, not more) before the cycle would
  repeat — standard number theory (5 and 12 share no factor), proved here
  by exhaustive case split: both the starting note and the note being
  counted range over 12 concrete values, so all 144 branches are direct
  `{==}` checks, mechanically generated rather than hand-written.

Run `bend PROOF.bend` from the repo root: **all ten laws across all five
milestones** check, printing `All terms check.`

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

- A `match` can only scrutinize a parameter or a variable bound by a
  pattern — never a computed value, a plain `let` binding (`b = f(x);
  match b:` is rejected with the same message as matching `f(x)` directly),
  or a destructuring `let` on a computed value (`(a, b) = f(x)` hits it
  too, not just `match`). Every one of these needs a small named helper
  whose own parameter is the computed value, matched there instead. Also,
  a function must be defined before its first use (no forward references
  anywhere, not just for recursion), so genuine mutual recursion — even
  the indirect kind this project's proofs kept running into, where a
  boolean/`Maybe` dispatch helper (forced to exist by the rule above) needs
  to call back into the function that called it — has no fix short of
  merging the two into one function (`bend guide`'s own advice). None of
  this produced a bad error message once understood, but it took a few
  rounds with the compiler each time to see what was actually being asked.
- Multi-scrutinee `match a b:` requires `a b` in the exact order the
  parameters were declared in the enclosing `def`'s signature, even when
  neither is otherwise involved — this project's error was generic ("this
  name is a def or a consumed binder") until the fix (reorder the `def`'s
  parameters, or the `match`, to agree) was found by trial.
- A datatype's own kind (`Data` vs `Type`) is chosen once at its `type
  ... is Data:`/`is Type:` declaration and applies everywhere that type is
  used; `Chord` started `is Type` (Milestone 1-3's code never needed to
  reuse one) and had to become `is Data` once Milestone 4's helpers needed
  to reuse a chord within one function body — a one-line, fully
  backward-compatible change, since `Data` only adds capability.
- A `~` template parameter is inlined *per call site*, but the function's
  own body is still typechecked once, generically, before any inlining
  happens — so a proof obligation like `{==}` inside a template's body
  can't lean on a specific call site's arguments being concrete, even
  though every actual call is. `min7_shell`/`dom7_shell`/`maj7_shell`
  hit this trying to share one `shell_voicing(~third_iv, ~seventh_iv,
  root)`; the fix was the mundane one (three separate functions, no
  templates), not a workaround for the template mechanism itself.

No compiler crashes or incomprehensible errors were hit across any of the
five milestones; no GitHub issue filed yet — every obstacle here was either
already documented in `bend guide` (if easy to miss in the moment) or had a
clear, if generic, error message that a few rounds with the compiler
resolved.
