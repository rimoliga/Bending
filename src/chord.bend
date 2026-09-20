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

type Chord is Data:
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

# The other qualities a ii-V-i needs
# ----------------------------------
# min7 [0,3,7,10] and maj7 [0,4,7,11] complete the major ii-V-I;
# min7b5 (half-diminished, [0,3,6,10]) and dim7 ([0,3,6,9]) are what a
# *minor* ii-V-i is built from -- iiø7, V7 and a minor tonic -- and
# dim7 doubles as the passing chord every standard is full of.
#
# Note the guide tones: min7 and min7b5 share the same 3rd and 7th
# (intervals 3 and 10); the b5 is a chord *tone*, not a guide tone.
# That is exactly why the minor ii-V-i's guide-tone motion is the same
# as the major one's (see minor_ii_V_guide_tones in LAWS.bend), and
# why telling iim7 from iiø7 on the guitar needs a voicing that
# actually includes the 5th (src/exercise.bend's 3-note shapes).

def min7(root: Pc.Note) -> Chord:
  Chord{root, [0n, 3n, 7n, 10n]}

def maj7(root: Pc.Note) -> Chord:
  Chord{root, [0n, 4n, 7n, 11n]}

def min7b5(root: Pc.Note) -> Chord:
  Chord{root, [0n, 3n, 6n, 10n]}

def min7b5_third(root: Pc.Note) -> Pc.Note:
  Pc.transpose(3n, root)

def min7b5_fifth(root: Pc.Note) -> Pc.Note:
  Pc.transpose(6n, root)

def min7b5_seventh(root: Pc.Note) -> Pc.Note:
  Pc.transpose(10n, root)

def dim7(root: Pc.Note) -> Chord:
  Chord{root, [0n, 3n, 6n, 9n]}

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

# Drop-2 and drop-3 voicings
# --------------------------
# A closed voicing is its notes stacked as close together as
# possible, e.g. [root, 3rd, 5th, 7th]. Drop-2 takes the 2nd note from
# the top and drops it an octave; drop-3 takes the 3rd note from the
# top. Since a Note only tracks pitch class, "an octave down" is
# invisible -- both are just a reordering of the same 4 notes: drop-2
# moves index 2 to the front, drop-3 moves index 1 to the front. Any
# list that isn't exactly 4 notes long passes through unchanged (a
# total, if not musically meaningful, fallback).

def drop2(xs: List<Pc.Note>) -> List<Pc.Note>:
  match xs:
    case Nil{}:
      Nil{}
    case n0 <> t1:
      match t1:
        case Nil{}:
          n0 <> Nil{}
        case n1 <> t2:
          match t2:
            case Nil{}:
              n0 <> n1 <> Nil{}
            case n2 <> t3:
              match t3:
                case Nil{}:
                  n0 <> n1 <> n2 <> Nil{}
                case n3 <> t4:
                  match t4:
                    case Nil{}:
                      n2 <> n0 <> n1 <> n3 <> Nil{}
                    case n4 <> t5:
                      n0 <> n1 <> n2 <> n3 <> n4 <> t5

def drop3(xs: List<Pc.Note>) -> List<Pc.Note>:
  match xs:
    case Nil{}:
      Nil{}
    case n0 <> t1:
      match t1:
        case Nil{}:
          n0 <> Nil{}
        case n1 <> t2:
          match t2:
            case Nil{}:
              n0 <> n1 <> Nil{}
            case n2 <> t3:
              match t3:
                case Nil{}:
                  n0 <> n1 <> n2 <> Nil{}
                case n3 <> t4:
                  match t4:
                    case Nil{}:
                      n1 <> n0 <> n2 <> n3 <> Nil{}
                    case n4 <> t5:
                      n0 <> n1 <> n2 <> n3 <> n4 <> t5

def bump(b: Bool, n: Nat) -> Nat:
  match b:
    case True{}:
      1n+n
    case False{}:
      n

# how many times x occurs in xs, as pitch classes
def count(+x: Pc.Note, xs: List<Pc.Note>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      bump(Pc.is_eq(x, h), count(x, t))
