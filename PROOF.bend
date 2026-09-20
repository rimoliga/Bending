# PROOF.bend: the proofs. A law is a def whose type is the claim: a
# match is the case analysis, the self-call is the induction
# hypothesis, and %e : P rewrites the goal with the equation e.

import Base
import ./src/note.bend as Pc
import ./src/chord.bend as Ch
import ./src/negharm.bend as Nh
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
def notes_from_transpose(ivs: +List<Nat>, +k: Nat, +root: Pc.Note) ->
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

# Milestone 2: dominant 7ths, tritone substitution, inversion, negative harmony
# ==============================================================================

# transpose_period12: applying succ 12 times returns to the start.
# n must be concrete for succ to actually reduce, so this is a plain
# 12-way case split, not an induction.
def transpose_period12(n: Pc.Note) -> {Pc.transpose(12n, n) == n : Pc.Note}:
  match n:
    case Pc.C{}:
      {==}
    case Pc.Db{}:
      {==}
    case Pc.D{}:
      {==}
    case Pc.Eb{}:
      {==}
    case Pc.E{}:
      {==}
    case Pc.F{}:
      {==}
    case Pc.Gb{}:
      {==}
    case Pc.G{}:
      {==}
    case Pc.Ab{}:
      {==}
    case Pc.A{}:
      {==}
    case Pc.Bb{}:
      {==}
    case Pc.B{}:
      {==}

# transpose_add12: transposing by 12+a is the same as transposing by
# a: transpose_add turns it into "transpose by a, then by 12", and
# transpose_period12 cancels the "by 12".
def transpose_add12(+a: Nat, +n: Pc.Note) -> {Pc.transpose(Nat.add(12n, a), n) == Pc.transpose(a, n) : Pc.Note}:
  e1 = Laws.transpose_add(12n, a, n)
  # e1 : {Pc.transpose(a, Pc.transpose(12n, n)) == Pc.transpose(Nat.add(12n, a), n) : Pc.Note}
  e2c = Equal.cong(Pc.Note, Pc.Note, x => Pc.transpose(a, x), Pc.transpose(12n, n), n, transpose_period12(n))
  # e2c : {Pc.transpose(a, Pc.transpose(12n, n)) == Pc.transpose(a, n) : Pc.Note}
  Equal.trans(Pc.Note, Pc.transpose(Nat.add(12n, a), n), Pc.transpose(a, Pc.transpose(12n, n)), Pc.transpose(a, n),
    Equal.sym(Pc.Note, Pc.transpose(a, Pc.transpose(12n, n)), Pc.transpose(Nat.add(12n, a), n), e1), e2c)

# tritone_sub_guide_tones: X7's 3rd is transpose(4,root); its
# substitute's root is transpose(6,root), so the substitute's 7th is
# transpose(10,transpose(6,root)) == transpose(16,root) (transpose_add)
# == transpose(4,root) (transpose_add12, since 16 == 12+4): X7's 3rd.
# Symmetrically for the 7th, landing on transpose(10,root) directly
# (6+4 == 10, no wraparound needed).
def Laws.tritone_sub_guide_tones(root):
  e1 = Laws.transpose_add(6n, 10n, root)
  # e1 : {Pc.transpose(10n, Pc.transpose(6n, root)) == Pc.transpose(16n, root) : Pc.Note}
  e2 = transpose_add12(4n, root)
  # e2 : {Pc.transpose(16n, root) == Pc.transpose(4n, root) : Pc.Note}
  p1 = Equal.sym(Pc.Note, Pc.transpose(10n, Pc.transpose(6n, root)), Pc.transpose(4n, root),
    Equal.trans(Pc.Note, Pc.transpose(10n, Pc.transpose(6n, root)), Pc.transpose(16n, root),
      Pc.transpose(4n, root), e1, e2))
  # p1 : {Pc.transpose(4n, root) == Pc.transpose(10n, Pc.transpose(6n, root)) : Pc.Note}
  p2 = Equal.sym(Pc.Note, Pc.transpose(4n, Pc.transpose(6n, root)), Pc.transpose(10n, root),
    Laws.transpose_add(6n, 4n, root))
  # p2 : {Pc.transpose(10n, root) == Pc.transpose(4n, Pc.transpose(6n, root)) : Pc.Note}
  (p1, p2)

# Inversion
# ---------

def append_nil_r(xs: +List<Nat>) -> {Ch.append(xs, Nil{}) == xs : +List<Nat>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %append_nil_r(t) : {h <> Ch.append(t, Nil{}) == h <> _ : +List<Nat>}
      {==}

def append_assoc(xs: +List<Nat>, ys: +List<Nat>, zs: +List<Nat>) ->
  {Ch.append(Ch.append(xs, ys), zs) == Ch.append(xs, Ch.append(ys, zs)) : +List<Nat>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %append_assoc(t, ys, zs) : {h <> Ch.append(Ch.append(t, ys), zs) == h <> _ : +List<Nat>}
      {==}

# rotate_append: rotating append(t, ys) left by len(t) steps moves t
# to the back, landing on append(ys, t). Induction on t: each step
# peels the head h off the front, folds it onto ys via append_assoc,
# and the induction hypothesis finishes the rest.
def rotate_append(t: +List<Nat>, +ys: +List<Nat>) ->
  {Ch.rotate_iter(Ch.len(t), Ch.append(t, ys)) == Ch.append(ys, t) : +List<Nat>}:
  match t:
    case Nil{}:
      Equal.sym(+List<Nat>, Ch.append(ys, Nil{}), ys, append_nil_r(ys))
    case +h <> +r:
      c1 = Equal.cong(+List<Nat>, +List<Nat>, z => Ch.rotate_iter(Ch.len(r), z),
        Ch.append(Ch.append(r, ys), [h]), Ch.append(r, Ch.append(ys, [h])), append_assoc(r, ys, [h]))
      # c1 : {rotate_iter(len(r), append(append(r,ys),[h])) == rotate_iter(len(r), append(r,append(ys,[h]))) : List<Nat>}
      ih = rotate_append(r, Ch.append(ys, [h]))
      # ih : {rotate_iter(len(r), append(r,append(ys,[h]))) == append(append(ys,[h]), r) : List<Nat>}
      s1 = Equal.trans(+List<Nat>,
        Ch.rotate_iter(Ch.len(r), Ch.append(Ch.append(r, ys), [h])),
        Ch.rotate_iter(Ch.len(r), Ch.append(r, Ch.append(ys, [h]))),
        Ch.append(Ch.append(ys, [h]), r), c1, ih)
      # s1 : {rotate_iter(len(r), append(append(r,ys),[h])) == append(append(ys,[h]), r) : List<Nat>}
      Equal.trans(+List<Nat>,
        Ch.rotate_iter(Ch.len(r), Ch.append(Ch.append(r, ys), [h])),
        Ch.append(Ch.append(ys, [h]), r),
        Ch.append(ys, h <> r), s1, append_assoc(ys, [h], r))

def rotate_full(+xs: +List<Nat>) -> {Ch.rotate_iter(Ch.len(xs), xs) == xs : +List<Nat>}:
  e1 = rotate_append(xs, Nil{})
  # e1 : {rotate_iter(len(xs), append(xs,Nil{})) == xs : List<Nat>}  (append(Nil{},xs) defeq xs)
  e2c = Equal.cong(+List<Nat>, +List<Nat>, z => Ch.rotate_iter(Ch.len(xs), z),
    Ch.append(xs, Nil{}), xs, append_nil_r(xs))
  # e2c : {rotate_iter(len(xs), append(xs,Nil{})) == rotate_iter(len(xs), xs) : List<Nat>}
  Equal.trans(+List<Nat>, Ch.rotate_iter(Ch.len(xs), xs), Ch.rotate_iter(Ch.len(xs), Ch.append(xs, Nil{})), xs,
    Equal.sym(+List<Nat>, Ch.rotate_iter(Ch.len(xs), Ch.append(xs, Nil{})), Ch.rotate_iter(Ch.len(xs), xs), e2c), e1)

def Laws.invert_n_identity(c):
  match c:
    case Ch.Chord{root, intervals}:
      Equal.cong(+List<Nat>, Ch.Chord, ivs => Ch.Chord{root, ivs},
        Ch.rotate_iter(Ch.len(intervals), intervals), intervals, rotate_full(intervals))

# Negative harmony
# ----------------

def mirror_involution(n: Pc.Note) -> {Nh.mirror(Nh.mirror(n)) == n : Pc.Note}:
  match n:
    case Pc.C{}:
      {==}
    case Pc.Db{}:
      {==}
    case Pc.D{}:
      {==}
    case Pc.Eb{}:
      {==}
    case Pc.E{}:
      {==}
    case Pc.F{}:
      {==}
    case Pc.Gb{}:
      {==}
    case Pc.G{}:
      {==}
    case Pc.Ab{}:
      {==}
    case Pc.A{}:
      {==}
    case Pc.Bb{}:
      {==}
    case Pc.B{}:
      {==}

# neg_involution_core: negative_harmony conjugates mirror by a
# transpose of `idx` (= index(tonic)) and its complement `comp` (with
# idx+comp == 12 either way around, e1/e2). Shifting by comp then idx
# (or idx then comp) is a shift by 12, which transpose_period12 erases,
# so the two transposes around each `mirror` cancel and only the two
# `mirror`s remain, which cancel via mirror_involution.
def neg_involution_core(+idx: Nat, +comp: Nat,
  e1: {Nat.add(idx, comp) == 12n : Nat}, e2: {Nat.add(comp, idx) == 12n : Nat}, +n: Pc.Note) ->
  {Pc.transpose(idx, Nh.mirror(Pc.transpose(comp, Pc.transpose(idx, Nh.mirror(Pc.transpose(comp, n))))))
    == n : Pc.Note}:
  sA1 = Laws.transpose_add(idx, comp, Nh.mirror(Pc.transpose(comp, n)))
  # sA1 : {transpose(comp, transpose(idx, mirror(transpose(comp,n))))
  #         == transpose(Nat.add(idx,comp), mirror(transpose(comp,n))) : Pc.Note}
  sA2 = Equal.cong(Nat, Pc.Note, z => Pc.transpose(z, Nh.mirror(Pc.transpose(comp, n))), Nat.add(idx, comp), 12n, e1)
  sA3 = transpose_period12(Nh.mirror(Pc.transpose(comp, n)))
  sA = Equal.trans(Pc.Note, Pc.transpose(comp, Pc.transpose(idx, Nh.mirror(Pc.transpose(comp, n)))),
    Pc.transpose(Nat.add(idx, comp), Nh.mirror(Pc.transpose(comp, n))), Nh.mirror(Pc.transpose(comp, n)),
    sA1, Equal.trans(Pc.Note, Pc.transpose(Nat.add(idx, comp), Nh.mirror(Pc.transpose(comp, n))),
      Pc.transpose(12n, Nh.mirror(Pc.transpose(comp, n))), Nh.mirror(Pc.transpose(comp, n)), sA2, sA3))
  # sA : {transpose(comp, transpose(idx, mirror(transpose(comp,n)))) == mirror(transpose(comp,n)) : Pc.Note}
  sB = Equal.cong(Pc.Note, Pc.Note, z => Nh.mirror(z),
    Pc.transpose(comp, Pc.transpose(idx, Nh.mirror(Pc.transpose(comp, n)))), Nh.mirror(Pc.transpose(comp, n)), sA)
  sC = mirror_involution(Pc.transpose(comp, n))
  sD = Equal.trans(Pc.Note, Nh.mirror(Pc.transpose(comp, Pc.transpose(idx, Nh.mirror(Pc.transpose(comp, n))))),
    Nh.mirror(Nh.mirror(Pc.transpose(comp, n))), Pc.transpose(comp, n), sB, sC)
  # sD : {mirror(transpose(comp, transpose(idx, mirror(transpose(comp,n))))) == transpose(comp,n) : Pc.Note}
  sE = Equal.cong(Pc.Note, Pc.Note, z => Pc.transpose(idx, z),
    Nh.mirror(Pc.transpose(comp, Pc.transpose(idx, Nh.mirror(Pc.transpose(comp, n))))), Pc.transpose(comp, n), sD)
  # sE : {transpose(idx, mirror(transpose(comp, transpose(idx, mirror(transpose(comp,n))))))
  #         == transpose(idx, transpose(comp,n)) : Pc.Note}
  sF1 = Laws.transpose_add(comp, idx, n)
  sF2 = Equal.cong(Nat, Pc.Note, z => Pc.transpose(z, n), Nat.add(comp, idx), 12n, e2)
  sF3 = transpose_period12(n)
  sF = Equal.trans(Pc.Note, Pc.transpose(idx, Pc.transpose(comp, n)), Pc.transpose(Nat.add(comp, idx), n), n,
    sF1, Equal.trans(Pc.Note, Pc.transpose(Nat.add(comp, idx), n), Pc.transpose(12n, n), n, sF2, sF3))
  # sF : {transpose(idx, transpose(comp,n)) == n : Pc.Note}
  Equal.trans(Pc.Note,
    Pc.transpose(idx, Nh.mirror(Pc.transpose(comp, Pc.transpose(idx, Nh.mirror(Pc.transpose(comp, n)))))),
    Pc.transpose(idx, Pc.transpose(comp, n)), n, sE, sF)

def Laws.negative_harmony_involution(tonic, n):
  match tonic:
    case Pc.C{}:
      neg_involution_core(0n, 12n, {==}, {==}, n)
    case Pc.Db{}:
      neg_involution_core(1n, 11n, {==}, {==}, n)
    case Pc.D{}:
      neg_involution_core(2n, 10n, {==}, {==}, n)
    case Pc.Eb{}:
      neg_involution_core(3n, 9n, {==}, {==}, n)
    case Pc.E{}:
      neg_involution_core(4n, 8n, {==}, {==}, n)
    case Pc.F{}:
      neg_involution_core(5n, 7n, {==}, {==}, n)
    case Pc.Gb{}:
      neg_involution_core(6n, 6n, {==}, {==}, n)
    case Pc.G{}:
      neg_involution_core(7n, 5n, {==}, {==}, n)
    case Pc.Ab{}:
      neg_involution_core(8n, 4n, {==}, {==}, n)
    case Pc.A{}:
      neg_involution_core(9n, 3n, {==}, {==}, n)
    case Pc.Bb{}:
      neg_involution_core(10n, 2n, {==}, {==}, n)
    case Pc.B{}:
      neg_involution_core(11n, 1n, {==}, {==}, n)
