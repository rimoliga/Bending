# Bending: a jazz theory engine in Bend 2

A jazz-theory engine written in [Bend 2](https://github.com/bendlang/bend), a
language with dependent types and machine-checked proofs. Every milestone
states its laws in `LAWS.bend` and proves them in `PROOF.bend`; `bend
PROOF.bend` is the gate, and it must print `All terms check.` before a
milestone is considered done.

All five milestones and three later extensions are implemented, and **all 16
laws stated are proved** (`bend PROOF.bend` → `All terms check.`). Three gaps
the README once documented rather than papered over have since been closed
and are written up where they happened: Milestone 4's divide-and-conquer
wrapper (`solve_parallel`) shipped with its own boundedness unproved and was
closed with two more lemmas; `solve_chain`'s voice-leading *search* over
chord inversions — descoped once as blocked on mutual recursion — is now
real, and proved; and `solve_parallel` itself, which for a while traded
completeness for a guessed anchor, is now **provably equal to `solve_chain`**
for every progression, every bound and every anchor — not bounded when it
happens to succeed, but never wrong about whether it succeeds at all.

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
bend main.bend F minor 3  # flags: `minor` for iiø7-V7-im7, `3` for 3-note shells
python3 tools/fretboard.py --shape 3   # printable practice sheet (no deps)
```

## Status by milestone

(Then three extensions past the original five: more chord qualities, richer
voicings, and a renderer outside Bend. Same rule throughout — a feature that
deserves a law gets one, or the README says why it didn't.)

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

### Milestone 4 — Voice leading: done, all laws proved

`src/voicelead.bend`.

**Model.** `dist(x, y)` is circular pitch-class distance (0..6), built from
`Nat.sub`/`Nat.min`, no `Nat.mod` needed. `voices_bounded(xs, ys, n)` checks
every corresponding pair of two same-length note lists is within `n`
semitones; `chain_bounded(sol, anchor, n)` extends that down a whole list of
voicings, starting from a given anchor.

`solve_chain(chords, n, anchor)` walks a progression and, at each chord,
**searches among all of that chord's inversions** (`candidates`,
`Ch.invert_times`) for the first voicing within `n` semitones of the
previously chosen one, failing (`None`) at the first chord where no inversion
is close enough. The search is real: with a bound of 2 semitones, `C7 → F7`
is rejected in root position (every voice moves 5) and accepted as `[C, Eb,
F, A]`, F7's second inversion (voices move 0, 1, 2, 1) — a progression the
earlier, fixed-voicing version simply reported as unsolvable.

*This is the point that was previously descoped*, and the way back in was a
change of algorithm shape rather than a workaround. The blocked version wrote
the search and the progression walk as two phases calling into each other —
try a candidate, and *on success continue with the rest of the chords*, on
failure try the next candidate — which is genuine mutual recursion, and Bend
requires every function to be defined before its first use, with no cycles
(`bend guide`'s own advice, merging the two phases into one function with
eager both-branch evaluation, had been tried and made the resulting proof
worse, not better). The observation that dissolves it: **a candidate's
acceptance test depends only on the anchor, never on the rest of the
progression.** So the search can be a self-contained, singly recursive
function returning `Maybe<voicing>` (`search`, `search_pick`), and the walk
consumes its result. The one remaining obstacle — the walk's recursive call
needs the chosen voicing, which sits inside that `Maybe`, and Bend cannot
match a computed value inline — is handled by *projecting* the `Maybe` to a
plain voicing (`from_maybe_v`, with an unused default) **before** recursing,
and only then dispatching on the `Maybe` itself in `solve_chain_step`. The
projection's default is never observed: when the search returned `None`,
`solve_chain_step` discards the recursive result and returns `None` anyway.
Backtracking (undoing chord *k*'s choice because chord *k+3* later got stuck)
is still the genuinely mutually recursive algorithm and is still out of
scope; this is a greedy search, and the law is about what it does choose.

The proof follows the same skeleton as before, plus one new lemma about the
search itself: `search_sound` — whenever `search` returns a candidate, that
candidate really is within `n` of the anchor (induction on the candidate
list, with `search_pick_sound` mirroring `search_pick`'s `Bool` dispatch) —
and `from_maybe_some`, that projecting `Some{w}` gives back `w`. Those two
are exactly what `solve_chain_step_bounded` needs where the old proof could
appeal to the voicing being fixed.

`solve_parallel(chords, n, anchor)` was, for a while, the divide-and-conquer
version described in the paragraphs below (still true of the git history):
split the progression in half, run `solve_chain` on each half via a parallel
call, and since a real search means the right half's true anchor is whatever
the left half's search chose for its last chord — not known until the left
half finishes — guess that anchor (the left half's last chord's closed
voicing) and check the seam for real once both halves are in. That kept the
boundedness law true but cost completeness: at `n = 2` on `C7 F7 Bb7 Eb7`,
`solve_chain` finds a solution and `solve_parallel` returned `None`, because
the guess missed the actual inversion `solve_chain`'s search would pick.

**That gap is now closed.** `solve_parallel` is provably **equal** to
`solve_chain` — not just bounded when it happens to succeed, but the exact
same result, for every progression, every `n` and every anchor. No progression
`solve_chain` solves is ever lost to a bad guess, and none it rejects is ever
wrongly accepted.

#### Evaluating the idea before writing it: solve every candidate anchor, then select

The fix the task asked for evaluating first: instead of guessing *one* anchor
for the right half, solve it from *every* anchor the left half could
possibly hand off, and pick out the right one once the left half's real
answer is in.

- **Is the candidate-anchor set closed and finite?** Yes. Whatever
  `solve_chain` picks for any chord is, by construction of `search`/
  `search_pick`, literally one element of `candidates(that chord)` — a list
  of length `Ch.chord_len(c)` (3 for a triad, 4 for a seventh chord),
  computable from the chord alone, no search required to enumerate it. So
  the right half's real anchor is always one of `candidates(last_chord(left))`
  (or the progression's own anchor, if the left half is empty) — a small,
  known-in-advance set.
- **Does the design keep genuinely balanced parallel calls?** Only partly,
  and it's worth saying so plainly rather than glossing over it: solving the
  right half for *every* candidate (3–4 of them) means the right-hand branch
  of the top-level parallel call does 3–4× the work of the left-hand branch,
  even though both halves cover comparable-sized progressions — exactly the
  imbalance `bend guide` warns sub-ideal speedups come from. The fan-out
  *inside* `solve_from_each_anchor` itself is uniform (each candidate does
  one full `solve_chain(right, ...)`), so that part is fine; it's the
  top-level split that's lopsided. Measured in Milestone D below.
- **A simpler alternative?** Considered fusing the right-half results
  directly into a single traversal of the left half (thread the
  precomputed-per-candidate results in as the left walk reaches its last
  chord). That's more elegant on paper but **breaks the independence Bend's
  parallel call needs**: that fused function would need the right-half
  results as an *argument* before it can run, so it could never be one of
  two genuinely independent branches — no real parallelism left. The design
  that keeps real parallelism is: run `solve_chain(left, ...)` and
  `solve_from_each_anchor(right, candidates, n)` as the two independent
  halves of one parallel call, then do a cheap, sequential **selection**
  (comparing the left half's actual last voicing against the candidate list
  by value — `Pc.Note` is a closed 12-constructor enum, so this is decidable
  and cheap) once both are in. Verified empirically before committing to it:
  a Bend parallel call is transparent to the proof checker (`{==}` closes the
  equality between a parallel-let and its sequential unfolding), so this
  design costs nothing in proof weight relative to writing it sequentially.

No fundamental obstacle turned up — no law needed weakening and no
`@unsafe` was needed anywhere in this codebase.

#### Hito A — `solve_from_each_anchor`: a total function over anchors

```
def solve_from_each_anchor(cs: List<&2, +List<Pc.Note>>, right: +List<Ch.Chord>, +n: Nat) ->
  List<&2, Maybe<&2, List<&2, +List<Pc.Note>>>>
```

Given the right half and a list of candidate anchors, it returns one
`solve_chain` result per anchor — divide and conquer directly over the
(small) candidate list, one parallel call per cons cell (`a b =
solve_chain(right, n, h) solve_from_each_anchor(t, right, n)`; call with `!`
to fan out onto the GPU). Each element is independent of the others, so this
is exactly the shape `bend guide`'s own `pow2` example uses.

- `solve_from_each_anchor_sound`: the result for candidate `h` (the head of
  the list) is exactly `solve_chain(right, n, h)`, and the rest of the
  result list is the same computation over the rest of the candidates —
  stated structurally (`solve_from_each_anchor(h <> t, right, n) ==
  solve_chain(right, n, h) <> solve_from_each_anchor(t, right, n)`), so it
  covers every position by induction rather than needing an index. The proof
  is a bare `{==}`: Bend's checker treats a parallel-let as definitionally
  identical to its sequential unfolding, confirmed empirically before this
  milestone was written.

#### Hito B — the seam as a selection

`solve_parallel_split` now: compute `anchor_list = pick_anchor_list(last_chord(left),
anchor)` (candidates of the left half's last chord, or `[anchor]` if the left
half is empty); run `left_res right_results = solve_chain(left, n, anchor)
solve_from_each_anchor(anchor_list, right, n)` as one genuine parallel call
(neither branch needs the other's result); then, once both are in,
`solve_parallel_combine` picks — by value, via `select_result` and
`list_note_eq` (elementwise `Pc.Note` equality) — the entry of
`right_results` whose anchor matches the left half's *actual* last voicing,
and glues the two solutions together with the same `append_sol`/
`VL.solve_parallel_finish` finishing step `solve_chain` itself would use.
No guess, no verify-and-reject: the right answer was already computed
alongside the left half, and the seam just looks it up.

- `solve_parallel_eq_solve_chain`: `solve_parallel(chords, n, anchor) ==
  solve_chain(chords, n, anchor)` for every progression, every `n` and every
  anchor. The proof chains three pieces, all in `PROOF.bend`:
  - `split_at_append`: splitting a progression and appending the two halves
    back together is the identity (`append_chords_pair(split_at(k, xs)) ==
    xs`), a plain structural fact about `split_at`'s own recursion.
  - `solve_chain_append`: `solve_chain` is compositional —
    `solve_chain(xs ++ ys, n, anchor)` is exactly what solving `xs` first
    and, on success, solving `ys` from `xs`'s own last voicing (or `anchor`,
    if `xs` is empty) and appending would give. This is a fact purely about
    `solve_chain`'s own chord-by-chord recursion, with no mention of
    `solve_parallel` — the sequential answer to "what would splitting this
    by hand give you."
  - `solve_chain_left_selects_right`: the seam lemma proper. Whenever
    `solve_chain` solves a left half `xs` from `anchor`, the selection
    (`select_result` over `solve_from_each_anchor`'s precomputed results)
    picks out exactly what `solve_chain` would compute for the right half
    directly from `xs`'s real last voicing. Proved by induction on `xs`,
    bottoming out at a `search_select_agree` lemma (search's own choice is
    literally an element of the candidate list it walks, so re-selecting by
    value over the *same* list, with the *same* precomputed-per-candidate
    results threaded alongside, recovers the same answer) plus a small
    reanchoring step (`pick_anchor_list_indep`, `last_chord_some`) for
    non-last chords, whose candidate list doesn't depend on which anchor got
    it there. Combined with `split_at_append` and `solve_chain_append`, this
    closes the equality.
- `solve_parallel_bounded` is now exactly the corollary the task predicted:
  since `solve_parallel` and `solve_chain` agree completely, whenever
  `solve_parallel` succeeds so does `solve_chain` with the *same* solution,
  and `solve_chain_bounded` already covers that — no seam-specific
  boundedness argument is needed anymore.

#### Hito C — cleanup, and what stayed

`chain_bounded_reanchor` and `chain_bounded_append` — the lemmas that moved a
*bound* across a guessed-then-verified seam — are gone, not left dead: there
is no guess left to correct for, so nothing needs its bound transferred.
`pick_anchor` (the single-guess version) and `seam_ok`/`join_pick`/`join_sol`
(guess-then-verify) are replaced outright by `pick_anchor_list`,
`solve_from_each_anchor`, `select_result` and `solve_parallel_combine`.
`last_of`, `last_chord`, `append_sol`, `len_chords`, `split_cons` and
`split_at` are unchanged and still load-bearing. `VL.solve_parallel_finish`
is reused (not duplicated) as the reference "combine" step in the equality
proof itself, so the two finishing steps — solve_parallel's real one and the
proof's reference one — are the *same* function, not two functions a lemma
has to relate.

Verified by hand (`tools/` has no committed script for this — the point was
the fix, not a throwaway harness — but the commands below reproduce it: a
scratch file importing `src/voicelead.bend`, calling `VL.solve_chain` and
`VL.solve_parallel` on each progression and comparing the printed results):

| Progression | `n` | `solve_chain` | `solve_parallel` |
|---|---|---|---|
| C7 F7 Bb7 Eb7 | 2 | `Some [C E G Bb] [C Eb F A] [Bb D F Ab] [Bb Db Eb G]` | **same** (previously `None`) |
| C7 F7 Bb7 Eb7 | 5 | `Some [C E G Bb] [F A C Eb] [Bb D F Ab] [Eb G Bb Db]` | same |
| C7 F7 Bb7 Eb7 | 6 | `Some [C E G Bb] [F A C Eb] [Bb D F Ab] [Eb G Bb Db]` | same |
| Dm7 G7 Cmaj7 (odd length, 3) | 2 | `Some [D F A C] [D F G B] [C E G B]` | same |
| Dm7 G7 Cmaj7 (odd length, 3) | 6 | `Some [D F A C] [G B D F] [C E G B]` | same |
| C7 Am7 Dm7 G7 Cmaj7 (5 chords) | 2 | `Some [C E G Bb] [C E G A] [C D F A] [B D F G] [B C E G]` | same |
| C7 Am7 Dm7 G7 Cmaj7 (5 chords) | 6 | `Some [...]` (5 voicings) | same |
| C7 (one chord) | 2 | `Some [C E G Bb]` | same |
| C7 (one chord) | 6 | `Some [C E G Bb]` | same |
| C7 F7 Bb7 Eb7 | 0 | `None` | same (agreement holds in failure too) |
| C7 Am7 Dm7 G7 Cmaj7 | 0 | `None` | same |

`n = 2` on `C7 F7 Bb7 Eb7` is the case the old README flagged as
`solve_parallel` returning `None` where `solve_chain` succeeds; it now agrees
exactly, including the specific inversion chain.

#### Hito D — measuring the honest cost

Compiled to native with `clang 18.1.3` (`bend bench.bend -o bench_native`;
no `@unsafe`, no source changes needed — the guide's "clang 19+ with `!`"
caveat turned out not to bite here: a `!`-using program compiled and ran
fine on this GPU-less machine, clang 18, with no `.gpu` sidecar produced,
falling back to CPU per `bend guide`'s own description of that case).
No CUDA and no Metal are available in this environment (`/usr/local/cuda`
absent, no `nvidia-smi`), so GPU numbers below are not measured, only CPU —
plain parallel calls (no `!`) across the machine's 4 cores (`nproc`).

Progressions were built by repeating the `C7 F7 Bb7 Eb7` cell; anchor is C7's
closed voicing, `n = 6`. Times are milliseconds, `./bench_native --threads
K`:

| length | `solve_chain` (1 thread) | `solve_parallel` (1 thread) | `solve_chain` (4 threads) | `solve_parallel` (4 threads) |
|---:|---:|---:|---:|---:|
| 4 | 0 | 0 | 0 | 1 |
| 16 | 0 | 0 | 0 | 0 |
| 64 | 0 | 1 | 0 | 1 |
| 256 | 0 | 1 | 0 | 1 |
| 1,024 | 1 | 4 | 2 | 3 |
| 4,096 | 6 | 16 | 6 | 8 |
| 16,384 | 24 | 61 | 23 | 29 |
| 65,536 | 96 | 250 | 95 | 116 |
| 262,144 | 383 | 995 | 404 | 469 |

At the lengths the task named (4–256 chords), both versions run in low
single-digit milliseconds — too fast for either the split or the extra
candidate-solving work to show up against process/timer noise. Scaling well
past that (up to 262,144 chords) to get a stable signal: **`solve_parallel`
is slower than `solve_chain` at every length tested, on this 4-core
machine, whether run single- or multi-threaded.** Threading narrows the gap
substantially (2.6× slower on 1 thread → 1.16× slower on 4 threads at the
largest size), confirming the parallel calls are doing real work, but it
never closes it, and the ratio holds roughly steady as length grows rather
than shrinking toward 1 — consistent with the imbalance flagged in the
evaluation above (the right-hand branch does ~4× the left-hand branch's
work, since it solves every candidate anchor) rather than a fixed, amortizable
startup cost. No crossover length was found up to 262,144 chords, three
orders of magnitude past what was asked. Extrapolating from the model rather
than hoping: with `P` cores, the right half's own 4-way candidate fan-out
needs up to 4 cores just to bring its wall-clock down to roughly the left
half's, and only once *that* is saturated do additional cores help the outer
2-way split race the two halves concurrently — so on hardware with
meaningfully more cores than the chord's own arity (4, or 3 for a triad
progression), `solve_parallel`'s critical path should approach `max(left,
right) ≈ half the sequential length`, beating `solve_chain`'s full pass by
close to 2×. That regime is not reachable on this 4-core machine, and no
number of *chords* changes that — only more cores would. An honest number
beats a favorable demo: on this hardware, at every length asked for and
plenty beyond it, `solve_chain` wins.

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

Run `bend PROOF.bend` from the repo root: **all 13 laws across all five
milestones** check, printing `All terms check.` The three extensions below
add three more, for **16 in total**.

### Extension 1 — Half-diminished and diminished 7ths: done, all laws proved

`src/chord.bend`, `src/exercise.bend`.

**Model.** `min7b5(root)` is `[0, 3, 6, 10]` (half-diminished, the iiø7 of a
minor ii-V-i) and `dim7(root)` is `[0, 3, 6, 9]`; `min7` `[0, 3, 7, 10]` and
`maj7` `[0, 4, 7, 11]` fill out the qualities the engine had been building
ad hoc. `major_ii_v_i(tonic)` and `minor_ii_v_i(tonic)` (in
`src/exercise.bend`) return the three chords of each cadence as a
`+List<Chord>` — the form `solve_chain` consumes, so a minor ii-V-i can now
be voice-led by the same search as a major one.

The musically interesting part is what the two laws below say together.
`min7b5` and `min7` have the *same* 3rd and 7th: the flat 5 is a chord tone,
not a guide tone. So a guide-tone-only shell cannot tell iim7 from iiø7 —
which is a fact about the instrument, not a shortcoming of the model, and the
reason Extension 2's three-note shapes (which include the 5th) exist.

**Laws proved** (`LAWS.bend`, proofs in `PROOF.bend`):

- `dim7_minor_third_symmetry`: a dim7 transposed up a minor third is the
  same chord, note for note, as its own first inversion — the reason there
  are only three distinct dim7 chords in all of music and the reason the
  shape slides up the neck in minor thirds. The proof is almost free in
  this model: transposing by a concrete `k` is `k` applications of `succ`,
  so three of the four notes share a normal form outright, and only the
  last one — 12 half steps up from the original root, against that root
  itself — needs `transpose_period12`, congruenced into that one list slot.
- `minor_ii_V_guide_tones`: for every tonic, the iiø7's 3rd *is* the V7's
  7th (a common tone, held), and the iiø7's 7th sits one half step above
  the V7's 3rd (so that voice steps down by a half step). Second half is a
  bare `{==}` (both sides are 12 half steps above the tonic, same normal
  form, no wraparound); the first half needs the same wraparound argument
  as `tritone_sub_guide_tones`, since the V7's 7th is 7 + 10 = 17 half
  steps up and `transpose_add12` brings that back to 5.

### Extension 2 — Three-note shell voicings: done, all laws proved

`src/exercise.bend`, `main.bend`.

**Model.** The two-note shells leave the root to the bass player; the
three-note version puts it back, on **whichever of the two bass strings lands
closer to the 3rd's fret** (`root_pick`, a `Bool` dispatch, so — like every
other computed scrutinee in this project — it gets its own function, with
both candidate `Strings` built before the choice). That rule is not a
heuristic bolted on to make the proofs pass; it is what guitarists actually
do, and the shapes it produces are the textbook ones: in F, `ii Gm7  A10 D8
G10`, `V C7  E8 D8 G9`, `I Fmaj7  A8 D7 G9`. Fixing the root to the A string
instead fails the playability check outright for the V chord in 10 of 12
keys (its root sits a 5th up the A string while its guide tones have been
chased *down* toward the ii chord's — a 6-to-7-fret stretch); the compiler
said so, per key, before any of this was written up.

`shell3_strings(root, fD, fG)` takes the D- and G-string frets as given, so
the same code serves both the standalone per-quality shapes (`min7_shell3`,
`dom7_shell3`, `maj7_shell3`, `min7b5_shell3` — each proved playable for all
12 roots by the established 12-way-match-then-`{==}`, 48 checks in total) and
the voice-led progression (`ii_v_i_shells3`), where the frets are the chased
ones. `ii_v_i_minor_shells` and `ii_v_i_minor_shells3` are the minor cadence
iiø7 - V7 - im7 from Extension 1, in two and three notes; they reuse the
major cadence's ii and V frets outright, since `min7b5` and `min7` share both
guide tones, and only the tonic chord changes shape.

`main.bend` takes the shape and the mode as flags, in any order:

```
$ bend main.bend F 3          $ bend main.bend F minor 3
key F                         key F minor
ii Gm7  A10:R D8:3 G10:7      ii Gm7b5  A10:R D8:3 G10:7
V  C7  E8:R D8:7 G9:3         V  C7  E8:R D8:7 G9:3
I  Fmaj7  A8:R D7:3 G9:7      i  Fm7  A8:R D6:3 G8:7
```

Each line is the chord, then one `<string><fret>:<role>` token per *sounding*
string, low to high — muted strings print nothing, so a two-note shell prints
two tokens and a three-note shell three, and the default output is
byte-identical to what it was before this extension.

**Laws proved** (`LAWS.bend`, proof in `PROOF.bend`):

- `min7_shell3_sounds_root_3_7`: for every root, the three-note min7 shell
  sounds the root, the minor 3rd and the minor 7th, each exactly once.
  This is the part the `Voicing` type does *not* cover: that type
  guarantees a shape is playable, but says nothing about which pitch
  classes come out of it, and this shape juggles octaves (`nearest_fret`)
  and picks between two bass strings — exactly the kind of arithmetic that
  can quietly land on the wrong note. Checked by computation in all 12
  branches; changing the `3n` in the statement to `5n` makes `bend
  PROOF.bend` fail with `expected: 0n, observed: 1n`, so it is a real
  check and not a tautology.

### Extension 3 — Printable practice sheet: `tools/fretboard.py`

Outside Bend, by design: the calculation is what belongs in a proof assistant,
and a chord diagram is not a calculation. The script computes nothing about
music. It runs `bend main.bend <key>` once for each of the twelve keys **in
the cycle of fourths** (C F Bb Eb Ab Db Gb B E A D G — the order musicians
practice in, and the order `cycle_of_fourths_visits_all` proves really does
reach all twelve), parses the engine's minimal text output, and draws the 36
voicings as fretboard diagrams in one self-contained HTML page, styled for
paper: open it and print it, or "Save as PDF" from the print dialog.

```
python3 tools/fretboard.py                    # 36 voicings, two-note shells
python3 tools/fretboard.py --shape 3          # three-note shells
python3 tools/fretboard.py --minor --shape 3  # the minor cadence
python3 tools/fretboard.py --keys C,F -o x.html
```

No third-party packages and no network: inline SVG, the standard library, and
the `bend` on your `PATH` (or `--bend /path/to/bend`). Each dot is labelled
with the note it sounds — `R`, `3`, `7` — rather than a finger number, since
which notes are sounding is the whole point of a shell voicing; a hollow
circle above the nut is an open string, `×` is muted, and a number beside the
top line is the starting fret. Each key is one `break-inside: avoid` block,
so printing never splits a cadence across pages.

[`docs/ii-V-I-practice.html`](docs/ii-V-I-practice.html) is a generated sample
(the default: major, two-note shells, all twelve keys), committed so the
output can be looked at without a working Bend install.

The one piece of shared ground between the engine and the script is the
output format, so it is kept deliberately dumb: one line per chord, a degree,
a chord name, then one `<string><fret>:<role>` token per *sounding* string.
The script re-derives nothing — the fret window it draws is justified by a
fact Bend already proved (no voicing stretches more than four frets, one of
the three conditions in `playable`), which is why five frets always suffice.
It does check what it can: a malformed line, a missing chord or a key the
engine didn't recognize (`main.bend` falls back to C) is an error or a
warning, not a silently wrong diagram.

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
  to call back into the function that called it — has no *local* fix short
  of merging the two into one function (`bend guide`'s own advice). The
  third way out, which is what eventually unblocked `solve_chain`'s
  inversion search, is to notice that the cycle is often not essential:
  if the callee's decision doesn't actually depend on what the caller does
  next, it can return that decision as data (a `Maybe`) instead of calling
  back, and the caller consumes it — with the value projected out of the
  `Maybe` *before* the recursive call, since the call can't be made from
  inside a `match` that the recursion has to happen underneath. None of
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

- The "no forward references, no mutual recursion" rule bites even when the
  cycle runs through several helpers that each look purely local. Splitting
  `solve_chain_left_selects_right`'s induction step across separate
  `case_mid_chord`/`case_mid_chord_at` helpers (for readability) initially had
  the innermost one call the outer lemma recursively — a genuine cycle among
  named `def`s, since Bend checks the whole dependency graph, not just
  "does this specific call site terminate." The fix already used earlier in
  this project for the analogous `solve_chain_bounded` proof generalizes
  cleanly: the recursive call is made once, at the one point in the *outer*
  function where it's legal (self-recursion on the parameter that
  structurally shrinks), wrapped in a closure, and passed down through the
  helpers as an opaque function argument they *call* but never *reference by
  name* — so the dependency graph stays a DAG even though the computation is
  still recursive.
- The guide's `&x:A -> B` dependent-pair syntax needs wrapping parens when
  used as a parameter's type inside a `def`'s signature (`w: (&y: N -> {...})`,
  per `tests/proof/exists_witness.bend` in the compiler's own test suite) —
  without them the checker's error ("expected: an annotated term (cannot
  infer)") gives no hint that the fix is punctuation. Destructuring one is
  also restricted like any other match: only legal on a parameter, never on
  a fresh computed value, so a helper that receives one and a caller that
  builds one via a plain function call (not a witness already in hand) don't
  mix directly. `last_chord_some` (a nonempty chord list's last chord
  witness) sidesteps both issues by taking a continuation instead of
  returning a pair at all — the same closure-passing shape as the mutual
  recursion fix above, and arguably clearer for it.
- A `Nat` successor pattern's bound variable takes its reusable-quantity `+`
  with a space before the name, not glued to the `+` in the pattern:
  `case 1n+ +p:`, not `case 1n+p:` with `p` used twice in the body (which
  reports the generic "consumed more than once" on the *pattern line*, not
  on the actual second use). Once seen, mechanical to apply everywhere else
  it came up (`split_at_append`'s own recursion, mirroring `split_at`'s).
- In a multi-scrutinee `match k xs: case 0n c <> t: ...; case 1n+ +p c <> +t:
  ...`, the same positional binder (`t`, here) needs a *consistent* quantity
  annotation across every case that binds it, even cases that don't
  themselves reuse it — `case 0n c <> t:` (affine) alongside `case 1n+ +p c
  <> +t:` (reusable) for the same slot was rejected, with the error again
  pointing at an unrelated-looking line, until both cases agreed on `+t`.

No compiler crashes or incomprehensible errors were hit anywhere in this
project. Every obstacle above was either already documented in `bend guide`
(if easy to miss in the moment) or had a clear, if generic, error message
that a few rounds with the compiler resolved — with one exception, the
template one, which is written up as a bug report in
[`ISSUE_DRAFT.md`](ISSUE_DRAFT.md).

**That report is written and verified but not filed**: this environment's
GitHub access is scoped to this repository, so creating an issue on
`bendlang/bend` was refused, and neither attaching that repository to the
session nor a `gh` CLI was available. The draft is ready to paste as-is; it
searched the tracker first (#784 and #902 are different template problems),
states the mechanism, and asks for one of three concrete outcomes. Its three
runnable repro files are in [`tools/issue_repro/`](tools/issue_repro):
`template_proof.bend` fails, `template_proof_uncalled.bend` fails *identically
with no call site at all* — the clearest evidence that the body is checked
once rather than per instantiation — and `template_proof_workaround.bend`
checks.
