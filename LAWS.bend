# LAWS.bend: the laws for the jazz theory engine. The human states
# them here; PROOF.bend must prove them. Milestone 1 covers pitch
# classes (src/note.bend) and chords (src/chord.bend). Milestone 2
# covers dominant 7th chords, tritone substitution, chord inversion
# and negative harmony (also src/chord.bend and src/negharm.bend).

import Base
import ./src/note.bend as Pc
import ./src/chord.bend as Ch
import ./src/negharm.bend as Nh

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
