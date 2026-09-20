# negharm.bend: negative harmony.
#
# Negative harmony reflects every pitch class around an axis tied to a
# chosen tonic. `mirror` is that reflection for tonic C (axis at C
# itself: C stays put, and each other note swaps with the note the
# same distance away on the other side of the wheel; Gb, opposite C,
# stays put too). `negative_harmony(tonic, n)` reflects around any
# tonic by first shifting the wheel so that tonic sits where C sits,
# applying `mirror`, then shifting back -- the standard conjugation
# trick for reflecting around any center once you have one fixed
# reflection. (Some treatments place the axis at the midpoint between
# a tonic and its fifth rather than at the tonic itself; that is a
# different, half-step-shifted `mirror` table, proved an involution by
# the same argument.)
#
# `comp` is a note's complement to a full turn: index(n) + comp(n) is
# always 12 (checkable per case, since both are literals), which is
# exactly what lets the shift-and-shift-back cancel out (see
# neg_involution_core in PROOF.bend).

import Base
import ./note.bend as Pc

def mirror(n: Pc.Note) -> Pc.Note:
  match n:
    case Pc.C{}:
      Pc.C{}
    case Pc.Db{}:
      Pc.B{}
    case Pc.D{}:
      Pc.Bb{}
    case Pc.Eb{}:
      Pc.A{}
    case Pc.E{}:
      Pc.Ab{}
    case Pc.F{}:
      Pc.G{}
    case Pc.Gb{}:
      Pc.Gb{}
    case Pc.G{}:
      Pc.F{}
    case Pc.Ab{}:
      Pc.E{}
    case Pc.A{}:
      Pc.Eb{}
    case Pc.Bb{}:
      Pc.D{}
    case Pc.B{}:
      Pc.Db{}

def comp(n: Pc.Note) -> Nat:
  match n:
    case Pc.C{}:
      12n
    case Pc.Db{}:
      11n
    case Pc.D{}:
      10n
    case Pc.Eb{}:
      9n
    case Pc.E{}:
      8n
    case Pc.F{}:
      7n
    case Pc.Gb{}:
      6n
    case Pc.G{}:
      5n
    case Pc.Ab{}:
      4n
    case Pc.A{}:
      3n
    case Pc.Bb{}:
      2n
    case Pc.B{}:
      1n

def negative_harmony(+tonic: Pc.Note, n: Pc.Note) -> Pc.Note:
  Pc.transpose(Pc.index(tonic), mirror(Pc.transpose(comp(tonic), n)))
