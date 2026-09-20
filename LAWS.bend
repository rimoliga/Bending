# LAWS.bend: the laws for the jazz theory engine. The human states
# them here; PROOF.bend must prove them. Milestone 1 covers pitch
# classes (src/note.bend) and chords (src/chord.bend).

import Base
import ./src/note.bend as Pc
import ./src/chord.bend as Ch

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
