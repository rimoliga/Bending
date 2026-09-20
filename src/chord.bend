# chord.bend: a chord as a root pitch class plus a list of intervals
# (half steps up from the root). The absolute notes of a chord are
# read off by transposing the root by each interval in turn.
#
# Transposing a chord only ever moves its root; the interval list is
# untouched. `notes_transposed` computes what you'd get by instead
# transposing every already-materialized note of a chord by the same
# amount, so LAWS.bend can state that the two agree (transpose_
# preserves_intervals): moving the root and moving every note by the
# same amount are the same chord.

import Base
import ./note.bend as Pc

type Chord is Type:
  Chord{root: Pc.Note, intervals: List<Nat>}

# the absolute notes reachable from root by each interval in ivs
def notes_from(+root: Pc.Note, ivs: List<Nat>) -> List<Pc.Note>:
  match ivs:
    case Nil{}:
      Nil{}
    case h <> r:
      Pc.transpose(h, root) <> notes_from(root, r)

def notes(c: Chord) -> List<Pc.Note>:
  match c:
    case Chord{root, intervals}:
      notes_from(root, intervals)

def transpose(k: Nat, c: Chord) -> Chord:
  match c:
    case Chord{root, intervals}:
      Chord{Pc.transpose(k, root), intervals}

# every note of xs moved up by k half steps
def notes_transposed(xs: List<Pc.Note>, +k: Nat) -> List<Pc.Note>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> r:
      Pc.transpose(k, h) <> notes_transposed(r, k)
