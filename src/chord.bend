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
  Chord{root: Pc.Note, intervals: +List<Nat>}

# the absolute notes reachable from root by each interval in ivs
def notes_from(+root: Pc.Note, ivs: +List<Nat>) -> List<Pc.Note>:
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

# Dominant 7th chords and tritone substitution
# ---------------------------------------------
# A dominant 7th on `root` is the intervals [0, 4, 7, 10]: root,
# major 3rd, perfect 5th, minor 7th. Its tritone substitute swaps the
# root for the note a tritone (6 half steps) away, keeping the same
# shape -- exactly Chord.transpose by 6.

def dom7(root: Pc.Note) -> Chord:
  Chord{root, [0n, 4n, 7n, 10n]}

def dom7_third(root: Pc.Note) -> Pc.Note:
  Pc.transpose(4n, root)

def dom7_seventh(root: Pc.Note) -> Pc.Note:
  Pc.transpose(10n, root)

def tritone_sub(c: Chord) -> Chord:
  transpose(6n, c)

# Inversion
# ---------
# Inverting a chord once moves its lowest interval to the top: the
# bottom note becomes the top note (an octave up, but a Chord only
# tracks pitch classes, so "an octave up" is invisible here -- the
# interval list is simply rotated left by one). Inverting an n-note
# chord n times is a full rotation of its n intervals, so it returns
# the original list (see LAWS.bend's invert_n_identity).

def append(xs: +List<Nat>, ys: +List<Nat>) -> +List<Nat>:
  match xs:
    case Nil{}:
      ys
    case h <> t:
      h <> append(t, ys)

def rotate1(xs: +List<Nat>) -> +List<Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      append(t, [h])

def rotate_iter(k: Nat, xs: +List<Nat>) -> +List<Nat>:
  match k:
    case 0n:
      xs
    case 1n+p:
      rotate_iter(p, rotate1(xs))

def invert(c: Chord) -> Chord:
  match c:
    case Chord{root, intervals}:
      Chord{root, rotate1(intervals)}

def invert_times(c: Chord, k: Nat) -> Chord:
  match c:
    case Chord{root, intervals}:
      Chord{root, rotate_iter(k, intervals)}

def len(xs: +List<Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      1n+len(t)

def chord_len(c: Chord) -> Nat:
  match c:
    case Chord{root, intervals}:
      len(intervals)
