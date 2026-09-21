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

def candidates_go(remaining: Nat, +c: Ch.Chord, +offset: Nat) -> List<&2, +List<Pc.Note>>:
  match remaining:
    case 0n:
      Nil{}
    case 1n+r:
      harden(Ch.notes(Ch.invert_times(c, offset))) <> candidates_go(r, c, 1n+offset)

# every inversion of c, candidate 0 being its closed/root position
def candidates(+c: Ch.Chord) -> List<&2, +List<Pc.Note>>:
  candidates_go(Ch.chord_len(c), c, 0n)

# search: the first candidate within n semitones of anchor
# -------------------------------------------------------
# `search` is the piece that makes solve_chain a real search instead
# of a fixed choice, and it is deliberately a *separate, single-
# recursive* function returning Maybe: it decides one chord's voicing
# from the anchor alone, without ever needing to know what happens to
# the rest of the progression. That is what dissolves the mutual
# recursion that blocked the earlier attempt (see the note on
# solve_chain below).
#
# search_pick exists because Bend cannot match a computed value:
# `voices_bounded(anchor, h, n)` has to become a parameter of its own
# function to be matched on. Both of its branches' values are computed
# eagerly at the call site (the same shape as note.bend's read_step).

def search_pick(b: Bool, v: +List<Pc.Note>, rest: Maybe<&2, +List<Pc.Note>>) -> Maybe<&2, +List<Pc.Note>>:
  match b:
    case True{}:
      Some{v}
    case False{}:
      rest

def search(cs: List<&2, +List<Pc.Note>>, +anchor: +List<Pc.Note>, +n: Nat) -> Maybe<&2, +List<Pc.Note>>:
  match cs:
    case Nil{}:
      None{}
    case +h <> t:
      search_pick(voices_bounded(anchor, h, n), h, search(t, anchor, n))

# the searched voicing, or `d` when the search found nothing (in which
# case solve_chain fails anyway, so the value is never used -- it only
# has to exist so the recursive call can be made before the Maybe is
# inspected).
def from_maybe_v(m: Maybe<&2, +List<Pc.Note>>, +d: +List<Pc.Note>) -> +List<Pc.Note>:
  match m:
    case None{}:
      d
    case Some{v}:
      v

# solve_chain
# -----------
# Each chord contributes one voicing, chosen by `search` among *all*
# its inversions: the first one within n semitones of the previous
# chosen voicing. It fails (None) at the first chord where no
# inversion is close enough.
#
# The shape here is what makes that expressible. An earlier attempt
# wrote the search and the progression walk as two phases calling into
# each other -- try a candidate, and *on success continue with the
# rest of the chords*, on failure try the next candidate -- which is
# genuine mutual recursion, and Bend requires every function to be
# defined before its first use, with no cycles. The way out is not a
# trick but a change of algorithm shape: because the acceptance test
# for a candidate depends only on the anchor, never on the rest of the
# progression, the search can be a self-contained function returning
# `Maybe<voicing>` (`search`, above) and the walk can consume its
# result. The one remaining obstacle -- the walk's recursive call
# needs the chosen voicing, which is inside that Maybe, and Bend
# cannot match a computed value inline -- is handled by projecting the
# Maybe to a plain voicing with `from_maybe_v` *before* recursing, and
# only then dispatching on the Maybe in solve_chain_step. The
# projection's default is never observed: when the search returned
# None, solve_chain_step discards the recursive result and returns
# None.
#
# Backtracking (undoing chord k's choice because chord k+3 later got
# stuck) is still out of scope, and is genuinely the mutually
# recursive algorithm; this is a greedy search, and the law below is
# about what it does choose.

def solve_chain_step(chosen: Maybe<&2, +List<Pc.Note>>, rest_sol: Maybe<&2, List<&2, +List<Pc.Note>>>) ->
  Maybe<&2, List<&2, +List<Pc.Note>>>:
  match chosen rest_sol:
    case None{} None{}:
      None{}
    case None{} Some{vs}:
      None{}
    case Some{v} None{}:
      None{}
    case Some{v} Some{vs}:
      Some{v <> vs}

def solve_chain(chords: +List<Ch.Chord>, +n: Nat, +anchor: +List<Pc.Note>) ->
  Maybe<&2, List<&2, +List<Pc.Note>>>:
  match chords:
    case Nil{}:
      Some{Nil{}}
    case c <> rest:
      +chosen = search(candidates(c), anchor, n)
      solve_chain_step(chosen, solve_chain(rest, n, from_maybe_v(chosen, Nil{})))

# every consecutive pair, starting from anchor, is within n semitones
def chain_bounded(sol: List<&2, +List<Pc.Note>>, anchor: +List<Pc.Note>, +n: Nat) -> Bool:
  match sol:
    case Nil{}:
      True{}
    case +h <> t:
      voices_bounded(anchor, h, n) && chain_bounded(t, h, n)

# solve_parallel: divide and conquer, equal to solve_chain
# ----------------------------------------------------------
# The right half's real anchor is whatever voicing the left half's
# search picks for its last chord -- not known until the left half
# finishes. Rather than guess one anchor and verify the seam
# afterward (which can reject progressions solve_chain would have
# solved), solve the right half from *every* candidate anchor at
# once: the set of voicings the left half's last chord could produce
# is exactly `candidates(that chord)`, finite and known from the
# chord list alone, with no search needed to enumerate it. Once the
# left half is solved for real, pick out (by value, not by re-running
# any search) the right-half result that was computed from the left
# half's actual last voicing. That selection -- not a guess-then-
# verify -- is the seam.

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

# structural equality on note lists (Pc.Note is a closed 12-way enum,
# so this is a plain elementwise walk) -- the runtime piece that lets
# the seam *select* the right precomputed answer instead of guessing
# one and checking it.
def list_note_eq(xs: +List<Pc.Note>, ys: +List<Pc.Note>) -> Bool:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          True{}
        case hy <> ty:
          False{}
    case hx <> tx:
      match ys:
        case Nil{}:
          False{}
        case hy <> ty:
          Pc.is_eq(hx, hy) && list_note_eq(tx, ty)

# the anchors the right half could really need: every inversion of the
# left half's last chord (candidates already enumerates exactly that,
# finite and known from the chord alone), or just the progression's
# own anchor if the left half is empty -- the same case pick_anchor
# used to make, now returning the whole set instead of one guess.
def pick_anchor_list(m: Maybe<&2, Ch.Chord>, +anchor: +List<Pc.Note>) -> List<&2, +List<Pc.Note>>:
  match m:
    case None{}:
      anchor <> Nil{}
    case Some{c}:
      candidates(c)

# solve_from_each_anchor: solve the right half from every candidate
# anchor at once. Each element of cs is independent of the others --
# divide and conquer over the (small, chord-arity-bounded) anchor
# list, one parallel call per element. Call with `!` to fan out onto
# the GPU.
def solve_from_each_anchor(cs: List<&2, +List<Pc.Note>>, +right: +List<Ch.Chord>, +n: Nat) ->
  List<&2, Maybe<&2, List<&2, +List<Pc.Note>>>>:
  match cs:
    case Nil{}:
      Nil{}
    case +h <> t:
      a b = solve_chain(right, n, h) solve_from_each_anchor(t, right, n)
      a <> b

def select_result_pick(b: Bool, r: Maybe<&2, List<&2, +List<Pc.Note>>>,
  rest: Maybe<&2, List<&2, +List<Pc.Note>>>) -> Maybe<&2, List<&2, +List<Pc.Note>>>:
  match b:
    case True{}:
      r
    case False{}:
      rest

# picks, from the results solve_from_each_anchor computed for every
# candidate anchor, the one whose anchor really is `target` -- the
# left half's actual last voicing (or the progression's own anchor,
# when the left half was empty). `target` is always some element of
# `cs` on the one way this is ever called (see solve_chain_left_selects_right
# in PROOF.bend), so this always finds a match there; the two
# length-mismatch cases below never arise on that path, since cs and
# rs are always built to the same shape.
def select_result(cs: List<&2, +List<Pc.Note>>, rs: List<&2, Maybe<&2, List<&2, +List<Pc.Note>>>>,
  +target: +List<Pc.Note>) -> Maybe<&2, List<&2, +List<Pc.Note>>>:
  match cs rs:
    case Nil{} Nil{}:
      None{}
    case Nil{} r <> rt:
      None{}
    case h <> t Nil{}:
      None{}
    case h <> t r <> rt:
      select_result_pick(list_note_eq(target, h), r, select_result(t, rt, target))

def solve_parallel_finish(right_res: Maybe<&2, List<&2, +List<Pc.Note>>>,
  sol_left: List<&2, +List<Pc.Note>>) -> Maybe<&2, List<&2, +List<Pc.Note>>>:
  match right_res:
    case None{}:
      None{}
    case Some{sol_right}:
      Some{append_sol(sol_left, sol_right)}

# the seam is a selection, not a guess-then-verify: once the left half
# is solved for real, look up (by value) the right-half result that
# was computed from that real last voicing.
def solve_parallel_combine(left_res: Maybe<&2, List<&2, +List<Pc.Note>>>,
  right_results: List<&2, Maybe<&2, List<&2, +List<Pc.Note>>>>,
  anchor_list: List<&2, +List<Pc.Note>>, +anchor: +List<Pc.Note>) -> Maybe<&2, List<&2, +List<Pc.Note>>>:
  match left_res:
    case None{}:
      None{}
    case Some{+sol_left}:
      +real_anchor = last_of(sol_left, anchor)
      solve_parallel_finish(select_result(anchor_list, right_results, real_anchor), sol_left)

def solve_parallel_split(pair: +List<Ch.Chord> & +List<Ch.Chord>, +n: Nat, +anchor: +List<Pc.Note>) ->
  Maybe<&2, List<&2, +List<Pc.Note>>>:
  match pair:
    case (+left, right):
      +anchor_list = pick_anchor_list(last_chord(left), anchor)
      left_res right_results = solve_chain(left, n, anchor) solve_from_each_anchor(anchor_list, right, n)
      solve_parallel_combine(left_res, right_results, anchor_list, anchor)

def solve_parallel(+chords: +List<Ch.Chord>, +n: Nat, +anchor: +List<Pc.Note>) ->
  Maybe<&2, List<&2, +List<Pc.Note>>>:
  +half = Nat.div(len_chords(chords), 2n)
  solve_parallel_split(split_at(half, chords), n, anchor)
