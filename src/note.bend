# note.bend: pitch classes.
#
# A pitch class stands for one of the 12 notes of the chromatic scale,
# the Bend equivalent of Fin(12): a closed type with exactly 12 values.
# Base has no generic Fin(n), so the 12 values are given as an explicit
# enum instead of a Sigma of a U32 and a boundedness proof; that keeps
# every proof a plain structural induction instead of one that also
# carries a `< 12` witness through each step. `index`/`is_eq` below let
# other modules compare notes and print them.
#
# Transposition is "mod 12" arithmetic realized as iterated succession:
# transposing by i steps i applications of `succ`, the note-name wheel's
# own successor. This makes `transpose(n, a+b) == transpose(transpose(n,
# a), b)` (LAWS.bend's transpose_add) a one-line induction on `a`, with
# no need to reason about Nat's division-based `Nat.mod` at all.

import Base

type Note is Data:
  C{}
  Db{}
  D{}
  Eb{}
  E{}
  F{}
  Gb{}
  G{}
  Ab{}
  A{}
  Bb{}
  B{}

# the next note up a half step, wrapping from B back to C
def succ(n: Note) -> Note:
  match n:
    case C{}:
      Db{}
    case Db{}:
      D{}
    case D{}:
      Eb{}
    case Eb{}:
      E{}
    case E{}:
      F{}
    case F{}:
      Gb{}
    case Gb{}:
      G{}
    case G{}:
      Ab{}
    case Ab{}:
      A{}
    case A{}:
      Bb{}
    case Bb{}:
      B{}
    case B{}:
      C{}

# transpose n up by i half steps (i comes first: it is what shrinks)
def transpose(i: Nat, n: Note) -> Note:
  match i:
    case 0n:
      n
    case 1n+p:
      transpose(p, succ(n))

# 0..11, C is 0
def index(n: Note) -> Nat:
  match n:
    case C{}:
      0n
    case Db{}:
      1n
    case D{}:
      2n
    case Eb{}:
      3n
    case E{}:
      4n
    case F{}:
      5n
    case Gb{}:
      6n
    case G{}:
      7n
    case Ab{}:
      8n
    case A{}:
      9n
    case Bb{}:
      10n
    case B{}:
      11n

def is_eq(a: Note, b: Note) -> Bool:
  Nat.is_eq(index(a), index(b))

def show(n: Note) -> String:
  match n:
    case C{}:
      "C"
    case Db{}:
      "Db"
    case D{}:
      "D"
    case Eb{}:
      "Eb"
    case E{}:
      "E"
    case F{}:
      "F"
    case Gb{}:
      "Gb"
    case G{}:
      "G"
    case Ab{}:
      "Ab"
    case A{}:
      "A"
    case Bb{}:
      "Bb"
    case B{}:
      "B"

# parses a note name ("C", "Db", ... "B"); None on anything else
def read_step(eq: Bool, val: Note, next: Maybe<&2, Note>) -> Maybe<&2, Note>:
  match eq:
    case True{}:
      Some{val}
    case False{}:
      next

def read(+s: String) -> Maybe<&2, Note>:
  read_step(String.eq(s, "C"), C{},
    read_step(String.eq(s, "Db"), Db{},
      read_step(String.eq(s, "D"), D{},
        read_step(String.eq(s, "Eb"), Eb{},
          read_step(String.eq(s, "E"), E{},
            read_step(String.eq(s, "F"), F{},
              read_step(String.eq(s, "Gb"), Gb{},
                read_step(String.eq(s, "G"), G{},
                  read_step(String.eq(s, "Ab"), Ab{},
                    read_step(String.eq(s, "A"), A{},
                      read_step(String.eq(s, "Bb"), Bb{},
                        read_step(String.eq(s, "B"), B{}, None{}))))))))))))
