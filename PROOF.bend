# PROOF.bend: the proofs. A law is a def whose type is the claim: a
# match is the case analysis, the self-call is the induction
# hypothesis, and %e : P rewrites the goal with the equation e.

import Base
import ./src/note.bend as Pc
import ./src/chord.bend as Ch
import ./LAWS.bend as Laws

# Nat helpers
# ===========
# Base ships Nat.add but no algebra about it. These three mirror
# demos/proof_numerics/PROOF.bend's add_zero/add_succ/add_comm, proved
# here against Base's own Nat.add so transpose_comm below can use them.

def add_zero(a: Nat) -> {a == Nat.add(a, 0n) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+p == 1n+_ : Nat}
      {==}

def add_succ(a: Nat, -b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {2n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      %add_zero(b) : {b == _ : Nat}
      {==}
    case 1n+p:
      %add_succ(b, p) : {1n+Nat.add(p, b) == _ : Nat}
      %add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

# Milestone 1: pitch classes
# ===========================

# transpose_add: induction on a. transpose(0,n) computes to n and
# Nat.add(0,b) to b, so the base case is reflexivity. In the step, both
# sides of the goal compute (via transpose's and Nat.add's own 1n+_
# case) to exactly the induction hypothesis's type, so the recursive
# call closes it with no rewrite needed.
def Laws.transpose_add(a, b, n):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Laws.transpose_add(p, b, Pc.succ(n))

def Laws.transpose_zero(n):
  {==}

# transpose_comm: transposing by h then k lands on the same note as k
# then h, since both equal a single transpose by h+k (transpose_add)
# and Nat.add is commutative (add_comm).
def transpose_comm(+h: Nat, +k: Nat, +root: Pc.Note) ->
  {Pc.transpose(h, Pc.transpose(k, root)) == Pc.transpose(k, Pc.transpose(h, root)) : Pc.Note}:
  e1 = Laws.transpose_add(k, h, root)
  # e1 : {Pc.transpose(h, Pc.transpose(k, root)) == Pc.transpose(Nat.add(k, h), root) : Pc.Note}
  e2 = Laws.transpose_add(h, k, root)
  # e2 : {Pc.transpose(k, Pc.transpose(h, root)) == Pc.transpose(Nat.add(h, k), root) : Pc.Note}
  e3 = add_comm(k, h)
  # e3 : {Nat.add(k, h) == Nat.add(h, k) : Nat}
  e3c = Equal.cong(Nat, Pc.Note, i => Pc.transpose(i, root), Nat.add(k, h), Nat.add(h, k), e3)
  # e3c : {Pc.transpose(Nat.add(k, h), root) == Pc.transpose(Nat.add(h, k), root) : Pc.Note}
  step = Equal.trans(Pc.Note, Pc.transpose(h, Pc.transpose(k, root)),
    Pc.transpose(Nat.add(k, h), root), Pc.transpose(Nat.add(h, k), root), e1, e3c)
  # step : {Pc.transpose(h, Pc.transpose(k, root)) == Pc.transpose(Nat.add(h, k), root) : Pc.Note}
  Equal.trans(Pc.Note, Pc.transpose(h, Pc.transpose(k, root)),
    Pc.transpose(Nat.add(h, k), root), Pc.transpose(k, Pc.transpose(h, root)),
    step, Equal.sym(Pc.Note, Pc.transpose(k, Pc.transpose(h, root)), Pc.transpose(Nat.add(h, k), root), e2))

# notes_from(transpose(k, root), ivs) is the same list as
# notes_transposed(notes_from(root, ivs), k): induction on ivs. Each
# cons swaps the head's two transpositions with transpose_comm, then
# the tail closes by the induction hypothesis.
def notes_from_transpose(ivs: List<Nat>, +k: Nat, +root: Pc.Note) ->
  {Ch.notes_from(Pc.transpose(k, root), ivs) == Ch.notes_transposed(Ch.notes_from(root, ivs), k) : List<Pc.Note>}:
  match ivs:
    case Nil{}:
      {==}
    case +h <> r:
      eh = transpose_comm(h, k, root)
      # eh : {Pc.transpose(h, Pc.transpose(k, root)) == Pc.transpose(k, Pc.transpose(h, root)) : Pc.Note}
      et = notes_from_transpose(r, k, root)
      # et : {Ch.notes_from(Pc.transpose(k, root), r) == Ch.notes_transposed(Ch.notes_from(root, r), k) : List<Pc.Note>}
      s1 = Equal.cong(List<Pc.Note>, List<Pc.Note>, x => Pc.transpose(h, Pc.transpose(k, root)) <> x,
        Ch.notes_from(Pc.transpose(k, root), r), Ch.notes_transposed(Ch.notes_from(root, r), k), et)
      # s1 : {transpose(h,transpose(k,root)) <> notes_from(transpose(k,root),r)
      #        == transpose(h,transpose(k,root)) <> notes_transposed(notes_from(root,r),k) : List<Pc.Note>}
      s2 = Equal.cong(Pc.Note, List<Pc.Note>, x => x <> Ch.notes_transposed(Ch.notes_from(root, r), k),
        Pc.transpose(h, Pc.transpose(k, root)), Pc.transpose(k, Pc.transpose(h, root)), eh)
      # s2 : {transpose(h,transpose(k,root)) <> notes_transposed(notes_from(root,r),k)
      #        == transpose(k,transpose(h,root)) <> notes_transposed(notes_from(root,r),k) : List<Pc.Note>}
      Equal.trans(List<Pc.Note>,
        Pc.transpose(h, Pc.transpose(k, root)) <> Ch.notes_from(Pc.transpose(k, root), r),
        Pc.transpose(h, Pc.transpose(k, root)) <> Ch.notes_transposed(Ch.notes_from(root, r), k),
        Pc.transpose(k, Pc.transpose(h, root)) <> Ch.notes_transposed(Ch.notes_from(root, r), k), s1, s2)

def Laws.transpose_preserves_intervals(k, c):
  match c:
    case Ch.Chord{root, intervals}:
      notes_from_transpose(intervals, k, root)
