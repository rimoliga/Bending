# main.bend: ii-V-I exercise generator CLI.
#
#   bend main.bend <key>           # key: C, Db, D, Eb, E, F, Gb, G, Ab, A, Bb, B
#   bend main.bend <key> minor     # iiø7 - V7 - im7 instead of iim7 - V7 - Imaj7
#   bend main.bend <key> 3         # three-note shells (root on a bass string)
#   bend main.bend <key> minor 3   # both; flags are order-independent
#   bend main.bend                 # defaults to C major, two-note shells
#
# Output is minimal and textual on purpose (bend guide: strings are a
# linked list, so text processing is slow) -- one line per chord, the
# root, the quality, and then one `<string><fret>:<role>` token per
# sounding string, low to high (role R, 3 or 7). Anything prettier
# belongs outside Bend: tools/fretboard.py renders these same lines as
# printable fretboard diagrams.

import Base
import ./src/note.bend as Pc
import ./src/voicing.bend as Vc
import ./src/exercise.bend as Ex

# one token per string that actually sounds; muted strings print
# nothing at all, so a two-note shell prints two tokens and a
# three-note shell three.
def pos_str(label: String, p: Vc.Position, role: String) -> String:
  match p:
    case Vc.Muted{}:
      ""
    case Vc.Fret{f}:
      " " ++ label ++ Nat.show(f) ++ ":" ++ role

# The B and high E strings carry no shape this program emits, so they
# have no role to name; they are still printed (as "-") if one ever
# does, rather than silently dropped.
def strings_str(s: Vc.Strings, d_role: String, g_role: String) -> String:
  match s:
    case Vc.Strings{e2, a2, d3, g3, b3, e4}:
      pos_str("E", e2, "R") ++ pos_str("A", a2, "R") ++ pos_str("D", d3, d_role) ++
        pos_str("G", g3, g_role) ++ pos_str("B", b3, "-") ++ pos_str("e", e4, "-")

def voicing_str(v: Vc.Voicing, d_role: String, g_role: String) -> String:
  match v:
    case Vc.Voicing{s, ok}:
      strings_str(s, d_role, g_role)

def line(label: String, root: Pc.Note, quality: String, d_role: String, g_role: String,
  v: Vc.Voicing) -> String:
  label ++ " " ++ Pc.show(root) ++ quality ++ " " ++ voicing_str(v, d_role, g_role)

# ii and I put the 3rd on the D string and the 7th on the G string; V
# swaps them (see src/exercise.bend for why that is what makes the
# guide tones connect).
def show_triple(t: Vc.Voicing & Vc.Voicing & Vc.Voicing, +tonic: Pc.Note, ii_q: String,
  i_label: String, i_q: String) -> String:
  match t:
    case (vii, vV, vI):
      line("ii", Pc.transpose(2n, tonic), ii_q, "3", "7", vii) ++ "\n" ++
        line("V ", Pc.transpose(7n, tonic), "7", "7", "3", vV) ++ "\n" ++
        line(i_label, tonic, i_q, "3", "7", vI)

def show_exercise(minor: Bool, three: Bool, +tonic: Pc.Note) -> String:
  match minor three:
    case True{} True{}:
      "key " ++ Pc.show(tonic) ++ " minor\n" ++
        show_triple(Ex.ii_v_i_minor_shells3(tonic), tonic, "m7b5", "i ", "m7")
    case True{} False{}:
      "key " ++ Pc.show(tonic) ++ " minor\n" ++
        show_triple(Ex.ii_v_i_minor_shells(tonic), tonic, "m7b5", "i ", "m7")
    case False{} True{}:
      "key " ++ Pc.show(tonic) ++ "\n" ++
        show_triple(Ex.ii_v_i_shells3(tonic), tonic, "m7", "I ", "maj7")
    case False{} False{}:
      "key " ++ Pc.show(tonic) ++ "\n" ++
        show_triple(Ex.ii_v_i_shells(tonic), tonic, "m7", "I ", "maj7")

# Flags are looked up by name anywhere in the argument list, so their
# order doesn't matter and the key is simply the first argument.
# flag_step exists because a match cannot scrutinize a computed value
# (here String.eq's result), the same reason src/note.bend's `read`
# has a read_step.
def flag_step(eq: Bool, rest_has: Bool) -> Bool:
  match eq:
    case True{}:
      True{}
    case False{}:
      rest_has

def has_flag(+flag: String, args: +List<String>) -> Bool:
  match args:
    case Nil{}:
      False{}
    case a <> rest:
      flag_step(String.eq(a, flag), has_flag(flag, rest))

def tonic_or_default(m: Maybe<&2, Pc.Note>) -> Pc.Note:
  match m:
    case None{}:
      Pc.C{}
    case Some{n}:
      n

def tonic_from_args(args: +List<String>) -> Pc.Note:
  match args:
    case Nil{}:
      Pc.C{}
    case a <> rest:
      tonic_or_default(Pc.read(a))

# IO.args() hands back an affine List<&1, String>, but the argument
# list is read three times below (two flags and the key), so it is
# rebuilt as a reusable +List<String> first -- the same "harden" move
# src/voicelead.bend makes for note lists.
def harden_args(xs: List<String>) -> +List<String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      h <> harden_args(t)

def run(args: List<String>) -> String:
  +as2 = harden_args(args)
  show_exercise(has_flag("minor", as2), has_flag("3", as2), tonic_from_args(as2))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    IO.print(run(args))
