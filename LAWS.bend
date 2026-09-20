# LAWS.bend: the laws for the jazz theory engine. The human states
# them here; PROOF.bend must prove them. Milestone 1 covers pitch
# classes (src/note.bend) and chords (src/chord.bend). Milestone 2
# covers dominant 7th chords, tritone substitution, chord inversion
# and negative harmony (also src/chord.bend and src/negharm.bend).

import Base
import ./src/note.bend as Pc
import ./src/chord.bend as Ch
import ./src/negharm.bend as Nh
import ./src/voicelead.bend as VL
import ./src/exercise.bend as Ex

# Milestone 1: pitch classes
# ==========================

# LAW: transposing by a, then by b, is the same as transposing by a+b
# in one step. (a comes first in the argument list: it is what the
# proof inducts on.)
law transpose_add:
  for a: Nat
  for b: Nat
  for n: Pc.Note
  {Pc.transpose(b, Pc.transpose(a, n)) == Pc.transpose(Nat.add(a, b), n) : Pc.Note}

# LAW: transposing by 0 changes nothing.
law transpose_zero:
  for n: Pc.Note
  {Pc.transpose(0n, n) == n : Pc.Note}

# LAW: transposing a chord (by moving only its root) gives the same
# notes as transposing every note of the original chord individually.
# In other words, transposition preserves a chord's set of intervals:
# the shape of the chord does not change, only where it sits.
law transpose_preserves_intervals:
  for k: Nat
  for c: Ch.Chord
  {Ch.notes(Ch.transpose(k, c)) == Ch.notes_transposed(Ch.notes(c), k) : List<Pc.Note>}

# Milestone 2: dominant 7ths, tritone substitution, inversion, negative harmony
# ==============================================================================

# LAW: for every X7 (a dominant 7th on `root`), its 3rd and 7th match,
# as pitch classes, the 7th and 3rd of its tritone substitute (the
# dominant 7th a tritone, i.e. 6 half steps, away).
law tritone_sub_guide_tones:
  for +root: Pc.Note
  {Ch.dom7_third(root) == Ch.dom7_seventh(Pc.transpose(6n, root)) : Pc.Note} &
  {Ch.dom7_seventh(root) == Ch.dom7_third(Pc.transpose(6n, root)) : Pc.Note}

# LAW: inverting an n-note chord n times returns the original chord.
law invert_n_identity:
  for c: Ch.Chord
  {Ch.invert_times(c, Ch.chord_len(c)) == c : Ch.Chord}

# LAW: negative harmony is an involution: applying it twice (around
# the same tonic) is the identity.
law negative_harmony_involution:
  for tonic: Pc.Note
  for n: Pc.Note
  {Nh.negative_harmony(tonic, Nh.negative_harmony(tonic, n)) == n : Pc.Note}

# Milestone 3: guitar voicings
# ============================
# Voicing (src/voicing.bend) is a dependent pair of guitar string
# positions and a proof they are playable (fret_bounds_ok,
# finger_count_ok and stretch_ok all hold): an unplayable Voicing
# cannot be constructed, so there is no separate law to state for
# that part -- it is the type itself. What remains is the one
# explicit law the milestone asks for: drop-2 and drop-3 reorder a
# closed voicing's notes without changing which pitch classes, or how
# many of each, are present.

# LAW: for every 4-note closed voicing, drop-2 produces the same
# pitch classes, the same number of times each, as the original --
# i.e. a permutation of the same set.
law drop2_is_permutation:
  for +n0: Pc.Note
  for +n1: Pc.Note
  for +n2: Pc.Note
  for +n3: Pc.Note
  for +x: Pc.Note
  {Ch.count(x, Ch.drop2([n0, n1, n2, n3])) == Ch.count(x, [n0, n1, n2, n3]) : Nat}

# LAW: same, for drop-3.
law drop3_is_permutation:
  for +n0: Pc.Note
  for +n1: Pc.Note
  for +n2: Pc.Note
  for +n3: Pc.Note
  for +x: Pc.Note
  {Ch.count(x, Ch.drop3([n0, n1, n2, n3])) == Ch.count(x, [n0, n1, n2, n3]) : Nat}

# Milestone 4: voice leading
# ==========================

# LAW: whenever VL.solve_chain finds a solution for a progression, no
# voice in that solution ever moves more than n semitones between two
# consecutive chords (counting the move from the given starting
# anchor into the first chord).
law solve_chain_bounded:
  for chords: +List<Ch.Chord>
  for +n: Nat
  for +anchor: +List<Pc.Note>
  for sol: List<&2, +List<Pc.Note>>
  for e: {VL.solve_chain(chords, n, anchor) == Some{sol} : Maybe<&2, List<&2, +List<Pc.Note>>>}
  {VL.chain_bounded(sol, anchor, n) == True{} : Bool}

# LAW: same as solve_chain_bounded, for solve_parallel's split/join.
law solve_parallel_bounded:
  for +chords: +List<Ch.Chord>
  for +n: Nat
  for +anchor: +List<Pc.Note>
  for sol: List<&2, +List<Pc.Note>>
  for e: {VL.solve_parallel(chords, n, anchor) == Some{sol} : Maybe<&2, List<&2, +List<Pc.Note>>>}
  {VL.chain_bounded(sol, anchor, n) == True{} : Bool}

# Milestone 5: exercise generator
# ================================

# LAW: starting anywhere and repeatedly moving by a perfect 4th visits
# every one of the 12 pitch classes exactly once (count 1, for every
# pitch class, not zero and not more) before the cycle would repeat.
law cycle_of_fourths_visits_all:
  for start: Pc.Note
  for x: Pc.Note
  {Ch.count(x, Ex.cycle_of_fourths(start)) == 1n : Nat}
