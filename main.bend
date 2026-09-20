# main.bend: ii-V-I exercise generator CLI.
#
#   bend main.bend <key>     # key: C, Db, D, Eb, E, F, Gb, G, Ab, A, Bb, B
#   bend main.bend           # defaults to C
#
# Output is minimal and textual on purpose (bend guide: strings are a
# linked list, so text processing is slow) -- one line per chord, the
# root, the quality, and the two guide tones as `<string><fret>:<role>`
# (role 3 or 7). Anything prettier belongs outside Bend.

import Base
import ./src/note.bend as Pc
import ./src/voicing.bend as Vc
import ./src/exercise.bend as Ex

def fret_str(p: Vc.Position) -> String:
  match p:
    case Vc.Muted{}:
      "x"
    case Vc.Fret{f}:
      Nat.show(f)

def voicing_dg(v: Vc.Voicing) -> Vc.Position & Vc.Position:
  match v:
    case Vc.Voicing{s, ok}:
      match s:
        case Vc.Strings{e2, a2, d3, g3, b3, e4}:
          (d3, g3)

def line(label: String, root: Pc.Note, quality: String, d_role: String, g_role: String,
  dg: Vc.Position & Vc.Position) -> String:
  match dg:
    case (d, g):
      label ++ " " ++ Pc.show(root) ++ quality ++ "  D" ++ fret_str(d) ++ ":" ++ d_role ++
        " G" ++ fret_str(g) ++ ":" ++ g_role

def show_triple(t: Vc.Voicing & Vc.Voicing & Vc.Voicing, +tonic: Pc.Note) -> String:
  match t:
    case (vii, vV, vI):
      line("ii", Pc.transpose(2n, tonic), "m7", "3", "7", voicing_dg(vii)) ++ "\n" ++
        line("V ", Pc.transpose(7n, tonic), "7", "7", "3", voicing_dg(vV)) ++ "\n" ++
        line("I ", tonic, "maj7", "3", "7", voicing_dg(vI))

def show_exercise(+tonic: Pc.Note) -> String:
  "key " ++ Pc.show(tonic) ++ "\n" ++ show_triple(Ex.ii_v_i_shells(tonic), tonic)

def tonic_or_default(m: Maybe<&2, Pc.Note>) -> Pc.Note:
  match m:
    case None{}:
      Pc.C{}
    case Some{n}:
      n

def tonic_from_args(args: List<String>) -> Pc.Note:
  match args:
    case Nil{}:
      Pc.C{}
    case a <> rest:
      tonic_or_default(Pc.read(a))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    IO.print(show_exercise(tonic_from_args(args)))
