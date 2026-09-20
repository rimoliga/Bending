# voicelead.bend: voice leading over a chord progression.
#
# A candidate voicing for a chord is one of its inversions (Milestone
# 2's Ch.invert_times), materialized to a +List<Pc.Note> (Data-kinded:
# it ends up carried inside a reusable Maybe, so every voicing list in
# this file is +List<Pc.Note>, not the plain List<Pc.Note>). Candidate
# 0 is the chord's own closed/root-position voicing.
#
# solve_chain walks a progression, and at each chord picks the first
# candidate whose every voice is within N semitones of the previous
# chosen voicing (or of the given starting anchor, for the first
# chord) -- "first", not a true argmin search over total cost, is a
# deliberate simplification: it keeps the boundedness law a direct
# consequence of how a candidate gets accepted, not a fact that has to
# be re-derived about a global optimum. It fails (returns None) the
# moment no candidate at some chord is within bound; PROOF.bend's law
# is only about the chains that do succeed.

import Base
import ./note.bend as Pc
import ./chord.bend as Ch

def raw_diff_pick(le: Bool, a: Nat, b: Nat) -> Nat:
  match le:
    case True{}:
      Nat.sub(b, a)
    case False{}:
      Nat.sub(a, b)

# circular distance between two pitch classes, 0..6
def raw_diff(+a: Nat, +b: Nat) -> Nat:
  raw_diff_pick(Nat.is_le(a, b), a, b)

def dist(x: Pc.Note, y: Pc.Note) -> Nat:
  +d = raw_diff(Pc.index(x), Pc.index(y))
  Nat.min(d, Nat.sub(12n, d))

# every corresponding pair of xs, ys is within n semitones (mismatched
# lengths are vacuously fine -- unused in practice, since a
# progression's chords all carry the same voice count)
def voices_bounded(xs: +List<Pc.Note>, ys: +List<Pc.Note>, +n: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case hx <> tx:
      match ys:
        case Nil{}:
          True{}
        case hy <> ty:
          Nat.is_le(dist(hx, hy), n) && voices_bounded(tx, ty, n)

# Candidates
# ----------

# Ch.notes returns a plain List<Pc.Note>; rebuild it as +List<Pc.Note>
# (every element is already Data, so this is just re-affirming that).
def harden(xs: List<Pc.Note>) -> +List<Pc.Note>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      h <> harden(t)

def candidates_go(remaining: Nat, +c: Ch.Chord, +offset: Nat) -> List<+List<Pc.Note>>:
  match remaining:
    case 0n:
      Nil{}
    case 1n+r:
      harden(Ch.notes(Ch.invert_times(c, offset))) <> candidates_go(r, c, 1n+offset)

def candidates(+c: Ch.Chord) -> List<+List<Pc.Note>>:
  candidates_go(Ch.chord_len(c), c, 0n)

# solve_chain
# -----------
# Each chord contributes exactly one voicing: its closed/root-position
# candidate (candidates(c)'s own index 0). Searching *among* a chord's
# several inversions for the best one, and continuing the chain from
# whichever works, needs two phases (try a candidate; on success,
# process the rest of the chords) that each call back into the other
# -- genuine mutual recursion, which Bend disallows (a function must
# be defined before its first use, with no cycle). An early attempt at
# that search is why `candidates` above exists; it was descoped here
# in favor of a single, single-recursive function whose boundedness
# law (LAWS.bend, proved in PROOF.bend) is a plain induction on the
# chord list -- a proof beats a feature. Extending this to a genuine
# multi-candidate search, proved, is future work.

def solve_chain_pick(b: Bool, on_true: Maybe<&2, List<&2, +List<Pc.Note>>>, v: +List<Pc.Note>) ->
  Maybe<&2, List<&2, +List<Pc.Note>>>:
  match b on_true:
    case True{} None{}:
      None{}
    case True{} Some{vs}:
      Some{v <> vs}
    case False{} None{}:
      None{}
    case False{} Some{vs}:
      None{}

def solve_chain(chords: +List<Ch.Chord>, +n: Nat, +anchor: +List<Pc.Note>) ->
  Maybe<&2, List<&2, +List<Pc.Note>>>:
  match chords:
    case Nil{}:
      Some{Nil{}}
    case c <> rest:
      +v = harden(Ch.notes(c))
      solve_chain_pick(voices_bounded(anchor, v, n), solve_chain(rest, n, v), v)

# every consecutive pair, starting from anchor, is within n semitones
def chain_bounded(sol: List<&2, +List<Pc.Note>>, anchor: +List<Pc.Note>, +n: Nat) -> Bool:
  match sol:
    case Nil{}:
      True{}
    case +h <> t:
      voices_bounded(anchor, h, n) && chain_bounded(t, h, n)

# solve_parallel: divide and conquer
# -----------------------------------
# Since every chord's own voicing here is always just its closed
# position (solve_chain never searches -- see the note above), the
# two halves of a split progression have no real data dependency on
# each other: the anchor the right half needs is exactly the closed
# voicing of the last chord of the left half, computable straight from
# the chord list, without running the left half's search first. That
# is what makes `a b = solve_chain(...) solve_chain(...)` a genuine
# parallel call rather than one waiting on the other. Call this with
# `!` (`solve_parallel!(...)`) to run the split on the GPU.

def len_chords(xs: +List<Ch.Chord>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case c <> t:
      1n+len_chords(t)

def split_cons(c: Ch.Chord, pair: +List<Ch.Chord> & +List<Ch.Chord>) -> +List<Ch.Chord> & +List<Ch.Chord>:
  match pair:
    case (l, r):
      (c <> l, r)

def split_at(k: Nat, xs: +List<Ch.Chord>) -> +List<Ch.Chord> & +List<Ch.Chord>:
  match k xs:
    case 0n Nil{}:
      (Nil{}, Nil{})
    case 0n c <> t:
      (Nil{}, c <> t)
    case 1n+p Nil{}:
      (Nil{}, Nil{})
    case 1n+p c <> t:
      split_cons(c, split_at(p, t))

def last_chord(xs: +List<Ch.Chord>) -> Maybe<&2, Ch.Chord>:
  match xs:
    case Nil{}:
      None{}
    case c <> +t:
      match t:
        case Nil{}:
          Some{c}
        case c2 <> t2:
          last_chord(t)

def pick_anchor(m: Maybe<&2, Ch.Chord>, +anchor: +List<Pc.Note>) -> +List<Pc.Note>:
  match m:
    case None{}:
      anchor
    case Some{c}:
      harden(Ch.notes(c))

# the last voicing of sol, or anchor if sol is empty
def last_of(sol: List<&2, +List<Pc.Note>>, +anchor: +List<Pc.Note>) -> +List<Pc.Note>:
  match sol:
    case Nil{}:
      anchor
    case h <> +t:
      match t:
        case Nil{}:
          h
        case h2 <> t2:
          last_of(t, h)

def append_sol(xs: List<&2, +List<Pc.Note>>, ys: List<&2, +List<Pc.Note>>) -> List<&2, +List<Pc.Note>>:
  match xs:
    case Nil{}:
      ys
    case h <> t:
      h <> append_sol(t, ys)

def join_sol(l: Maybe<&2, List<&2, +List<Pc.Note>>>, r: Maybe<&2, List<&2, +List<Pc.Note>>>) ->
  Maybe<&2, List<&2, +List<Pc.Note>>>:
  match l r:
    case None{} None{}:
      None{}
    case None{} Some{rs}:
      None{}
    case Some{ls} None{}:
      None{}
    case Some{ls} Some{rs}:
      Some{append_sol(ls, rs)}

def solve_parallel_split(pair: +List<Ch.Chord> & +List<Ch.Chord>, +n: Nat, +anchor: +List<Pc.Note>) ->
  Maybe<&2, List<&2, +List<Pc.Note>>>:
  match pair:
    case (+left, right):
      +mid_anchor = pick_anchor(last_chord(left), anchor)
      left_res right_res = solve_chain(left, n, anchor) solve_chain(right, n, mid_anchor)
      join_sol(left_res, right_res)

def solve_parallel(+chords: +List<Ch.Chord>, +n: Nat, +anchor: +List<Pc.Note>) ->
  Maybe<&2, List<&2, +List<Pc.Note>>>:
  +half = Nat.div(len_chords(chords), 2n)
  solve_parallel_split(split_at(half, chords), n, anchor)
