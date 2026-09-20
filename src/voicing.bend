# voicing.bend: guitar voicings that are playable by construction.
#
# Six strings, standard tuning, low to high: E, A, D, G, B, E. A
# Position is either muted or fretted (0 = open, 1..15 = a fretted
# note); frets go up to 15. `playable` computes, as a Bool, whether a
# Strings value obeys the three rules a human hand obeys:
#   - every fret is at most 15 (fret_bounds_ok)
#   - at most 4 strings are actually pressed down -- open strings and
#     muted strings need no finger, so they don't count
#     (finger_count_ok)
#   - among the pressed frets, the highest and lowest are at most 4
#     frets apart (stretch_ok)
#
# `Voicing` pairs a `Strings` with a proof that `playable` computes to
# `True`. Since that proof's type is an equality of two concrete Bool
# computations, it exists only when the strings really are playable
# (Bool's two constructors are distinct, so `{False{} == True{} :
# Bool}` has no proof) -- an unplayable `Voicing` cannot be built,
# `@unsafe` aside.

import Base
import ./note.bend as Pc

type Position is Data:
  Muted{}
  Fret{f: Nat}

type Strings is Data:
  Strings{e2: Position, a2: Position, d3: Position, g3: Position, b3: Position, e4: Position}

def fret_ok(pos: Position) -> Bool:
  match pos:
    case Muted{}:
      True{}
    case Fret{f}:
      Nat.is_le(f, 15n)

def fret_bounds_ok(s: Strings) -> Bool:
  match s:
    case Strings{e2, a2, d3, g3, b3, e4}:
      fret_ok(e2) && fret_ok(a2) && fret_ok(d3) && fret_ok(g3) && fret_ok(b3) && fret_ok(e4)

# Some{f} when pos is actually pressed down (a fretted note, f > 0);
# None for a muted or open string.
def pressed(pos: Position) -> Maybe<&2, Nat>:
  match pos:
    case Muted{}:
      None{}
    case Fret{f}:
      match f:
        case 0n:
          None{}
        case 1n+p:
          Some{f}

def maybe_cons(m: Maybe<&2, Nat>, xs: +List<Nat>) -> +List<Nat>:
  match m:
    case None{}:
      xs
    case Some{v}:
      v <> xs

def pressed_list(s: Strings) -> +List<Nat>:
  match s:
    case Strings{e2, a2, d3, g3, b3, e4}:
      maybe_cons(pressed(e2), maybe_cons(pressed(a2), maybe_cons(pressed(d3),
        maybe_cons(pressed(g3), maybe_cons(pressed(b3), maybe_cons(pressed(e4), Nil{}))))))

def list_len(xs: +List<Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      1n+list_len(t)

def finger_count_ok(s: Strings) -> Bool:
  Nat.is_le(list_len(pressed_list(s)), 4n)

def list_max_go(xs: +List<Nat>, +acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      list_max_go(t, Nat.max(h, acc))

def list_min_go(xs: +List<Nat>, +acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      list_min_go(t, Nat.min(h, acc))

# empty or singleton: no stretch. Otherwise the highest and lowest
# pressed fret, seeded from the head, must be within 4 of each other.
def stretch_ok(xs: +List<Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +h <> +t:
      Nat.is_le(Nat.sub(list_max_go(t, h), list_min_go(t, h)), 4n)

def playable(+s: Strings) -> Bool:
  fret_bounds_ok(s) && finger_count_ok(s) && stretch_ok(pressed_list(s))

type Voicing is Type:
  Voicing{strings: Strings, ok: {playable(strings) == True{} : Bool}}

# x32010: the open C major shape. Muted low E; A string 3rd fret (C);
# D string 2nd fret (E); G string open; B string 1st fret (C); high E
# open. Pressed frets [3, 2, 1]: 3 fingers, stretch 3-1 = 2.
def example_c_open() -> Voicing:
  Voicing{Strings{Muted{}, Fret{3n}, Fret{2n}, Fret{0n}, Fret{1n}, Fret{0n}}, {==}}

# Reading off the pitch classes a voicing actually sounds
# ---------------------------------------------------------

def note_of(open: Pc.Note, pos: Position) -> Maybe<&2, Pc.Note>:
  match pos:
    case Muted{}:
      None{}
    case Fret{f}:
      Some{Pc.transpose(f, open)}

def maybe_cons_note(m: Maybe<&2, Pc.Note>, xs: List<Pc.Note>) -> List<Pc.Note>:
  match m:
    case None{}:
      xs
    case Some{v}:
      v <> xs

def strings_notes(s: Strings) -> List<Pc.Note>:
  match s:
    case Strings{e2, a2, d3, g3, b3, e4}:
      maybe_cons_note(note_of(Pc.E{}, e2), maybe_cons_note(note_of(Pc.A{}, a2),
        maybe_cons_note(note_of(Pc.D{}, d3), maybe_cons_note(note_of(Pc.G{}, g3),
          maybe_cons_note(note_of(Pc.B{}, b3), maybe_cons_note(note_of(Pc.E{}, e4), Nil{}))))))

def notes(v: Voicing) -> List<Pc.Note>:
  match v:
    case Voicing{strings, ok}:
      strings_notes(strings)
