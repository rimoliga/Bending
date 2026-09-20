# PROOF.bend: the proofs. A law is a def whose type is the claim: a
# match is the case analysis, the self-call is the induction
# hypothesis, and %e : P rewrites the goal with the equation e.

import Base
import ./src/note.bend as Pc
import ./src/chord.bend as Ch
import ./src/negharm.bend as Nh
import ./src/voicelead.bend as VL
import ./src/exercise.bend as Ex
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

# Milestone 3: guitar voicings
# =============================
# The playability part of this milestone needs no proof here: Voicing
# (src/voicing.bend) pairs Strings with a proof that `playable`
# computes to True, and since that's an equality between two concrete
# Bool computations, the type itself is uninhabited for unplayable
# strings -- there is nothing left for PROOF.bend to establish. What
# remains is drop-2/drop-3 preserving the pitch-class multiset.

def bump_swap(a: Bool, b: Bool, -n: Nat) -> {Ch.bump(a, Ch.bump(b, n)) == Ch.bump(b, Ch.bump(a, n)) : Nat}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# swapping the first two elements of a list doesn't change how many
# times x occurs in it
def count_swap_adjacent(+x: Pc.Note, a: Pc.Note, b: Pc.Note, t: List<Pc.Note>) ->
  {Ch.count(x, a <> b <> t) == Ch.count(x, b <> a <> t) : Nat}:
  bump_swap(Pc.is_eq(x, a), Pc.is_eq(x, b), Ch.count(x, t))

# drop2([n0,n1,n2,n3]) == [n2,n0,n1,n3]: two adjacent swaps move n2 to
# the front (n1<->n2, then n0<->n2), each preserving count.
def Laws.drop2_is_permutation(n0, n1, n2, n3, x):
  s1 = count_swap_adjacent(x, n1, n2, n3 <> Nil{})
  # s1 : {count(x, n1<>n2<>n3<>Nil{}) == count(x, n2<>n1<>n3<>Nil{}) : Nat}
  step1 = Equal.cong(Nat, Nat, z => Ch.bump(Pc.is_eq(x, n0), z),
    Ch.count(x, n1 <> n2 <> n3 <> Nil{}), Ch.count(x, n2 <> n1 <> n3 <> Nil{}), s1)
  # step1 : {count(x, n0<>n1<>n2<>n3<>Nil{}) == count(x, n0<>n2<>n1<>n3<>Nil{}) : Nat}
  step2 = count_swap_adjacent(x, n0, n2, n1 <> n3 <> Nil{})
  # step2 : {count(x, n0<>n2<>n1<>n3<>Nil{}) == count(x, n2<>n0<>n1<>n3<>Nil{}) : Nat}
  combined = Equal.trans(Nat, Ch.count(x, n0 <> n1 <> n2 <> n3 <> Nil{}),
    Ch.count(x, n0 <> n2 <> n1 <> n3 <> Nil{}), Ch.count(x, n2 <> n0 <> n1 <> n3 <> Nil{}), step1, step2)
  # combined : {count(x, n0<>n1<>n2<>n3<>Nil{}) == count(x, n2<>n0<>n1<>n3<>Nil{}) : Nat}
  Equal.sym(Nat, Ch.count(x, n0 <> n1 <> n2 <> n3 <> Nil{}), Ch.count(x, n2 <> n0 <> n1 <> n3 <> Nil{}), combined)

# drop3([n0,n1,n2,n3]) == [n1,n0,n2,n3]: one adjacent swap (n0<->n1).
def Laws.drop3_is_permutation(n0, n1, n2, n3, x):
  step = count_swap_adjacent(x, n0, n1, n2 <> n3 <> Nil{})
  # step : {count(x, n0<>n1<>n2<>n3<>Nil{}) == count(x, n1<>n0<>n2<>n3<>Nil{}) : Nat}
  Equal.sym(Nat, Ch.count(x, n0 <> n1 <> n2 <> n3 <> Nil{}), Ch.count(x, n1 <> n0 <> n2 <> n3 <> Nil{}), step)

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

# Milestone 4: voice leading
# ===========================

# generic Maybe lemmas: None{} and Some{_} are distinct, and Some is
# injective. Both by the guide's discrimination-via-motive technique.

def maybe_disc(-A: Data, m: Maybe<&2, A>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{v}:
      Empty

def none_ne_some(-A: Data, x: A, e: {None{} == Some{x} : Maybe<&2, A>}) -> Empty:
  %e : maybe_disc(A, _)
  Unit{}

def some_prj(-A: Data, d: A, m: Maybe<&2, A>) -> A:
  match m:
    case None{}:
      d
    case Some{v}:
      v

def some_inj(-A: Data, a: A, b: A, e: {Some{a} == Some{b} : Maybe<&2, A>}) -> {a == b : A}:
  %e : {a == some_prj(A, a, _) : A}
  {==}

# search soundness
# ----------------
# The one fact about the candidate search the boundedness law needs:
# whenever search returns a candidate, that candidate really is within
# n semitones of the anchor. (The converse -- that search finds one
# whenever any exists -- is true too, but nothing below needs it.)
#
# search_pick_sound mirrors search_pick's own case split. `vbe`
# carries back the connection a generic Bool parameter forgets: the
# call site always passes b = voices_bounded(anchor, v, n) itself, so
# it can always supply {==} for it, and matching b == True{} then
# turns vbe into exactly the fact we want about the accepted
# candidate.

def search_pick_sound(b: Bool, v: +List<Pc.Note>, rest: Maybe<&2, +List<Pc.Note>>,
  +anchor: +List<Pc.Note>, +n: Nat, w: +List<Pc.Note>,
  vbe: {VL.voices_bounded(anchor, v, n) == b : Bool},
  e: {VL.search_pick(b, v, rest) == Some{w} : Maybe<&2, +List<Pc.Note>>},
  ih: @w2: +List<Pc.Note> -> {rest == Some{w2} : Maybe<&2, +List<Pc.Note>>} ->
    {VL.voices_bounded(anchor, w2, n) == True{} : Bool}) ->
  {VL.voices_bounded(anchor, w, n) == True{} : Bool}:
  match b:
    case True{}:
      ev = some_inj(+List<Pc.Note>, v, w, e)
      # ev : {v == w : +List<Pc.Note>}, vbe : {voices_bounded(anchor,v,n) == True{} : Bool}
      %ev : {VL.voices_bounded(anchor, _, n) == True{} : Bool}
      vbe
    case False{}:
      ih(w, e)

def search_sound(cs: List<&2, +List<Pc.Note>>, +anchor: +List<Pc.Note>, +n: Nat, w: +List<Pc.Note>,
  e: {VL.search(cs, anchor, n) == Some{w} : Maybe<&2, +List<Pc.Note>>}) ->
  {VL.voices_bounded(anchor, w, n) == True{} : Bool}:
  match cs:
    case Nil{}:
      Empty.absurd({VL.voices_bounded(anchor, w, n) == True{} : Bool}, none_ne_some(+List<Pc.Note>, w, e))
    case +h <> +t:
      search_pick_sound(VL.voices_bounded(anchor, h, n), h, VL.search(t, anchor, n), anchor, n, w, {==}, e,
        w2 => e2 => search_sound(t, anchor, n, w2, e2))

# from_maybe_v's default is never observed on the success path: when
# the search returned Some{w}, projecting it gives back w.
def from_maybe_some(m: Maybe<&2, +List<Pc.Note>>, +d: +List<Pc.Note>, w: +List<Pc.Note>,
  e: {m == Some{w} : Maybe<&2, +List<Pc.Note>>}) -> {VL.from_maybe_v(m, d) == w : +List<Pc.Note>}:
  es = Equal.sym(Maybe<&2, +List<Pc.Note>>, m, Some{w}, e)
  %es : {VL.from_maybe_v(_, d) == w : +List<Pc.Note>}
  {==}

# solve_chain_step_bounded: whenever solve_chain_step(chosen,
# rest_sol) succeeds with `sol`, both arguments were Some -- chosen
# with some candidate w, rest_sol with some tail vs -- and sol == w <>
# vs (the three None cases are absurd, since None{} == Some{sol} has
# no proof). Three facts are then threaded in from the call site,
# each as a function parameter because a generic parameter forgets
# where it came from:
#   hv : when chosen is Some{w}, the voicing the recursive call was
#        made with (from_maybe_v(chosen, Nil{})) is that same w;
#   hb : when chosen is Some{w}, w is within n of the anchor -- this
#        is search_sound, and it is what makes the *searched* voicing,
#        not just a fixed one, provably bounded;
#   ih : the outer induction hypothesis on the rest of the chords.
def solve_chain_step_bounded(chosen: Maybe<&2, +List<Pc.Note>>,
  rest_sol: Maybe<&2, List<&2, +List<Pc.Note>>>, v: +List<Pc.Note>,
  +anchor: +List<Pc.Note>, +n: Nat, sol: List<&2, +List<Pc.Note>>,
  hv: @w: +List<Pc.Note> -> {chosen == Some{w} : Maybe<&2, +List<Pc.Note>>} -> {v == w : +List<Pc.Note>},
  hb: @w: +List<Pc.Note> -> {chosen == Some{w} : Maybe<&2, +List<Pc.Note>>} ->
    {VL.voices_bounded(anchor, w, n) == True{} : Bool},
  e: {VL.solve_chain_step(chosen, rest_sol) == Some{sol} : Maybe<&2, List<&2, +List<Pc.Note>>>},
  ih: @vs: List<&2, +List<Pc.Note>> -> {rest_sol == Some{vs} : Maybe<&2, List<&2, +List<Pc.Note>>>} ->
    {VL.chain_bounded(vs, v, n) == True{} : Bool}) ->
  {VL.chain_bounded(sol, anchor, n) == True{} : Bool}:
  match chosen rest_sol:
    case None{} None{}:
      Empty.absurd({VL.chain_bounded(sol, anchor, n) == True{} : Bool}, none_ne_some(List<&2, +List<Pc.Note>>, sol, e))
    case None{} Some{vs}:
      Empty.absurd({VL.chain_bounded(sol, anchor, n) == True{} : Bool}, none_ne_some(List<&2, +List<Pc.Note>>, sol, e))
    case Some{w} None{}:
      Empty.absurd({VL.chain_bounded(sol, anchor, n) == True{} : Bool}, none_ne_some(List<&2, +List<Pc.Note>>, sol, e))
    case Some{+w} Some{+vs}:
      es = some_inj(List<&2, +List<Pc.Note>>, w <> vs, sol, e)
      # es : {w <> vs == sol : List<&2, +List<Pc.Note>>}
      ev = hv(w, {==})
      # ev : {v == w : +List<Pc.Note>}
      bw = hb(w, {==})
      # bw : {voices_bounded(anchor, w, n) == True{} : Bool}
      ok = ih(vs, {==})
      # ok : {chain_bounded(vs, v, n) == True{} : Bool} -- restated about w, the
      # candidate actually consed on, via ev (the recursive call was made with
      # from_maybe_v(chosen, Nil{}), which is w whenever chosen is Some{w}).
      okw = Equal.trans(Bool, VL.chain_bounded(vs, w, n), VL.chain_bounded(vs, v, n), True{},
        Equal.cong(+List<Pc.Note>, Bool, z => VL.chain_bounded(vs, z, n), w, v,
          Equal.sym(+List<Pc.Note>, v, w, ev)), ok)
      # okw : {chain_bounded(vs, w, n) == True{} : Bool}
      c1 = Equal.cong(Bool, Bool, z => z && VL.chain_bounded(vs, w, n), VL.voices_bounded(anchor, w, n), True{}, bw)
      c2 = Equal.cong(Bool, Bool, z => True{} && z, VL.chain_bounded(vs, w, n), True{}, okw)
      combined = Equal.trans(Bool, VL.voices_bounded(anchor, w, n) && VL.chain_bounded(vs, w, n),
        True{} && VL.chain_bounded(vs, w, n), True{}, c1, c2)
      # combined : {chain_bounded(w <> vs, anchor, n) == True{} : Bool}
      %es : {VL.chain_bounded(_, anchor, n) == True{} : Bool}
      combined

def Laws.solve_chain_bounded(chords, n, anchor, sol, e):
  match chords:
    case Nil{}:
      es = some_inj(List<&2, +List<Pc.Note>>, Nil{}, sol, e)
      # es : {Nil{} == sol : List<&2, +List<Pc.Note>>}
      %es : {VL.chain_bounded(_, anchor, n) == True{} : Bool}
      {==}
    case +c <> +rest:
      +chosen = VL.search(VL.candidates(c), anchor, n)
      +v = VL.from_maybe_v(chosen, Nil{})
      solve_chain_step_bounded(chosen, VL.solve_chain(rest, n, v), v, anchor, n, sol,
        w => e2 => from_maybe_some(chosen, Nil{}, w, e2),
        w => e2 => search_sound(VL.candidates(c), anchor, n, w, e2),
        e, vs => e2 => Laws.solve_chain_bounded(rest, n, v, vs, e2))

# Milestone 5: exercise generator
# =================================

# cycle_of_fourths_visits_all: exhaustive case split. Both start and x
# range over the 12 concrete notes, so cycle_of_fourths(start) fully
# computes to a 12-element concrete list and count(x, that list) fully
# computes to a literal in every one of the 144 branches -- a direct
# {==} each time, the same technique as transpose_period12 and
# mirror_involution, just over two notes instead of one.
def Laws.cycle_of_fourths_visits_all(start, x):
  match start:
    case Pc.C{}:
      match x:
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
    case Pc.Db{}:
      match x:
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
    case Pc.D{}:
      match x:
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
    case Pc.Eb{}:
      match x:
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
    case Pc.E{}:
      match x:
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
    case Pc.F{}:
      match x:
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
    case Pc.Gb{}:
      match x:
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
    case Pc.G{}:
      match x:
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
    case Pc.Ab{}:
      match x:
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
    case Pc.A{}:
      match x:
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
    case Pc.Bb{}:
      match x:
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
    case Pc.B{}:
      match x:
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

# Milestone 4 (continued): solve_parallel
# =========================================
# Closing the gap the README flagged: solve_parallel's own boundedness,
# on top of solve_chain's. Two pieces were missing: (1) chain_bounded
# composes across a list append, given the join point matches up, and
# (2) solve_chain's output always ends on the closed voicing of the
# progression's last chord, regardless of anchor -- which is exactly
# what makes solve_parallel's two halves independent, so it had better
# be true, and now it is proved, not just claimed.

# Bool helpers
# ------------

def bool_disc(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def false_ne_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : bool_disc(_)
  Unit{}

def and_true_l(a: Bool, +b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({a == True{} : Bool}, false_ne_true(e))

def and_true_r(a: Bool, +b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, false_ne_true(e))

# last_of / chain_bounded_append
# -------------------------------

# last_of(v <> vs, anchor) == last_of(vs, v): both sides reduce to the
# same term whether vs is empty (both give v) or not (both give
# last_of(vs, v) directly) -- a fact about last_of's own definition,
# not an induction.
def last_of_cons(v: +List<Pc.Note>, vs: List<&2, +List<Pc.Note>>, +anchor: +List<Pc.Note>) ->
  {VL.last_of(v <> vs, anchor) == VL.last_of(vs, v) : +List<Pc.Note>}:
  match vs:
    case Nil{}:
      {==}
    case h2 <> t2:
      {==}

# chain_bounded_append: if xs's own chain (from anchor) is bounded, and
# ys's chain (from xs's own last voicing, or anchor if xs is empty) is
# bounded, so is the chain of xs ++ ys (from anchor). Induction on xs.
def chain_bounded_append(xs: List<&2, +List<Pc.Note>>, ys: List<&2, +List<Pc.Note>>, +anchor: +List<Pc.Note>, +n: Nat,
  +bx: {VL.chain_bounded(xs, anchor, n) == True{} : Bool},
  by: {VL.chain_bounded(ys, VL.last_of(xs, anchor), n) == True{} : Bool}) ->
  {VL.chain_bounded(VL.append_sol(xs, ys), anchor, n) == True{} : Bool}:
  match xs:
    case Nil{}:
      by
    case +h <> +t:
      # bx : {voices_bounded(anchor,h,n) && chain_bounded(t,h,n) == True{} : Bool}
      bh = and_true_l(VL.voices_bounded(anchor, h, n), VL.chain_bounded(t, h, n), bx)
      bt = and_true_r(VL.voices_bounded(anchor, h, n), VL.chain_bounded(t, h, n), bx)
      # by : {chain_bounded(ys, last_of(h<>t, anchor), n) == True{} : Bool}
      byt_e = last_of_cons(h, t, anchor)
      byt_c = Equal.cong(+List<Pc.Note>, Bool, z => VL.chain_bounded(ys, z, n),
        VL.last_of(h <> t, anchor), VL.last_of(t, h), byt_e)
      byt = Equal.trans(Bool, VL.chain_bounded(ys, VL.last_of(t, h), n),
        VL.chain_bounded(ys, VL.last_of(h <> t, anchor), n), True{},
        Equal.sym(Bool, VL.chain_bounded(ys, VL.last_of(h <> t, anchor), n),
          VL.chain_bounded(ys, VL.last_of(t, h), n), byt_c), by)
      # byt : {chain_bounded(ys, last_of(t,h), n) == True{} : Bool}
      ih = chain_bounded_append(t, ys, h, n, bt, byt)
      # ih : {chain_bounded(append_sol(t,ys), h, n) == True{} : Bool}
      c1 = Equal.cong(Bool, Bool, z => Bool.and(z, VL.chain_bounded(VL.append_sol(t, ys), h, n)),
        VL.voices_bounded(anchor, h, n), True{}, bh)
      c2 = Equal.cong(Bool, Bool, z => Bool.and(True{}, z), VL.chain_bounded(VL.append_sol(t, ys), h, n), True{}, ih)
      Equal.trans(Bool, Bool.and(VL.voices_bounded(anchor, h, n), VL.chain_bounded(VL.append_sol(t, ys), h, n)),
        Bool.and(True{}, VL.chain_bounded(VL.append_sol(t, ys), h, n)), True{}, c1, c2)

# chain_bounded_reanchor
# ----------------------
# The seam lemma. A chain that is bounded from one anchor `a` is
# bounded from a different anchor `b` as soon as the single step from
# `b` into the chain's first voicing is itself within bound
# (VL.seam_ok) -- everything after that first step never mentions the
# anchor at all. This is what lets solve_parallel search its right
# half from a guessed anchor and still conclude something about the
# real one, once the two halves meet and the seam is checked.
def chain_bounded_reanchor(ys: List<&2, +List<Pc.Note>>, +a: +List<Pc.Note>, +b: +List<Pc.Note>, +n: Nat,
  e1: {VL.chain_bounded(ys, a, n) == True{} : Bool},
  e2: {VL.seam_ok(ys, b, n) == True{} : Bool}) ->
  {VL.chain_bounded(ys, b, n) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case +h <> +t:
      # e1 : {voices_bounded(a,h,n) && chain_bounded(t,h,n) == True{} : Bool}
      bt = and_true_r(VL.voices_bounded(a, h, n), VL.chain_bounded(t, h, n), e1)
      # e2 : {voices_bounded(b,h,n) == True{} : Bool}
      c1 = Equal.cong(Bool, Bool, z => z && VL.chain_bounded(t, h, n), VL.voices_bounded(b, h, n), True{}, e2)
      c2 = Equal.cong(Bool, Bool, z => True{} && z, VL.chain_bounded(t, h, n), True{}, bt)
      Equal.trans(Bool, VL.voices_bounded(b, h, n) && VL.chain_bounded(t, h, n),
        True{} && VL.chain_bounded(t, h, n), True{}, c1, c2)

# solve_parallel_bounded
# ------------------------
# join_pick_inv: join_pick only returns Some when the seam check
# passed, so on the success path `sbe` (supplied as {==} by the one
# call site) says seam_ok(rs, last_of(ls, anchor), n) == True{}.
# chain_bounded_reanchor then moves the right half's own bound from
# the guessed anchor `mid` onto the left half's real last voicing, and
# chain_bounded_append glues the two halves.
def join_pick_inv(ok: Bool, +ls: List<&2, +List<Pc.Note>>, +rs: List<&2, +List<Pc.Note>>,
  sol: List<&2, +List<Pc.Note>>, +anchor: +List<Pc.Note>, +n: Nat, +mid: +List<Pc.Note>,
  sbe: {VL.seam_ok(rs, VL.last_of(ls, anchor), n) == ok : Bool},
  e: {VL.join_pick(ok, ls, rs) == Some{sol} : Maybe<&2, List<&2, +List<Pc.Note>>>},
  bl: {VL.chain_bounded(ls, anchor, n) == True{} : Bool},
  br: {VL.chain_bounded(rs, mid, n) == True{} : Bool}) ->
  {VL.chain_bounded(sol, anchor, n) == True{} : Bool}:
  match ok:
    case True{}:
      es = some_inj(List<&2, +List<Pc.Note>>, VL.append_sol(ls, rs), sol, e)
      # es : {append_sol(ls, rs) == sol : List<&2, +List<Pc.Note>>}
      br2 = chain_bounded_reanchor(rs, mid, VL.last_of(ls, anchor), n, br, sbe)
      # br2 : {chain_bounded(rs, last_of(ls, anchor), n) == True{} : Bool}
      combined = chain_bounded_append(ls, rs, anchor, n, bl, br2)
      # combined : {chain_bounded(append_sol(ls, rs), anchor, n) == True{} : Bool}
      %es : {VL.chain_bounded(_, anchor, n) == True{} : Bool}
      combined
    case False{}:
      Empty.absurd({VL.chain_bounded(sol, anchor, n) == True{} : Bool}, none_ne_some(List<&2, +List<Pc.Note>>, sol, e))

def join_sol_inv(l: Maybe<&2, List<&2, +List<Pc.Note>>>, r: Maybe<&2, List<&2, +List<Pc.Note>>>,
  sol: List<&2, +List<Pc.Note>>, +anchor: +List<Pc.Note>, +n: Nat, +mid: +List<Pc.Note>,
  e: {VL.join_sol(l, r, anchor, n) == Some{sol} : Maybe<&2, List<&2, +List<Pc.Note>>>},
  bl: @ls: List<&2, +List<Pc.Note>> -> {l == Some{ls} : Maybe<&2, List<&2, +List<Pc.Note>>>} ->
    {VL.chain_bounded(ls, anchor, n) == True{} : Bool},
  br: @rs: List<&2, +List<Pc.Note>> -> {r == Some{rs} : Maybe<&2, List<&2, +List<Pc.Note>>>} ->
    {VL.chain_bounded(rs, mid, n) == True{} : Bool}) ->
  {VL.chain_bounded(sol, anchor, n) == True{} : Bool}:
  match l r:
    case None{} None{}:
      Empty.absurd({VL.chain_bounded(sol, anchor, n) == True{} : Bool}, none_ne_some(List<&2, +List<Pc.Note>>, sol, e))
    case None{} Some{rs}:
      Empty.absurd({VL.chain_bounded(sol, anchor, n) == True{} : Bool}, none_ne_some(List<&2, +List<Pc.Note>>, sol, e))
    case Some{ls} None{}:
      Empty.absurd({VL.chain_bounded(sol, anchor, n) == True{} : Bool}, none_ne_some(List<&2, +List<Pc.Note>>, sol, e))
    case Some{+ls} Some{+rs}:
      join_pick_inv(VL.seam_ok(rs, VL.last_of(ls, anchor), n), ls, rs, sol, anchor, n, mid, {==}, e,
        bl(ls, {==}), br(rs, {==}))

def solve_parallel_split_bounded(pair: +List<Ch.Chord> & +List<Ch.Chord>, +n: Nat, +anchor: +List<Pc.Note>,
  sol: List<&2, +List<Pc.Note>>,
  e: {VL.solve_parallel_split(pair, n, anchor) == Some{sol} : Maybe<&2, List<&2, +List<Pc.Note>>>}) ->
  {VL.chain_bounded(sol, anchor, n) == True{} : Bool}:
  match pair:
    case (+left, +right):
      +mid = VL.pick_anchor(VL.last_chord(left), anchor)
      join_sol_inv(VL.solve_chain(left, n, anchor), VL.solve_chain(right, n, mid), sol, anchor, n, mid, e,
        ls => e2 => Laws.solve_chain_bounded(left, n, anchor, ls, e2),
        rs => e2 => Laws.solve_chain_bounded(right, n, mid, rs, e2))

def Laws.solve_parallel_bounded(chords, n, anchor, sol, e):
  solve_parallel_split_bounded(VL.split_at(Nat.div(VL.len_chords(chords), 2n), chords), n, anchor, sol, e)

# Extension 1: half-diminished and diminished 7th chords
# =======================================================

# dim7_minor_third_symmetry: both sides are 4-note lists whose first
# three entries are literally the same term once transpose unfolds
# (transposing by a concrete k is k applications of succ, so
# transpose(3, transpose(3, root)) and transpose(6, root) share a
# normal form, and so on). Only the last entry differs: the transposed
# chord's 9th-above-its-own-root is succ applied 12 times to the
# original root, where the inversion has the original root itself --
# exactly transpose_period12, congruenced into that one list slot.
def Laws.dim7_minor_third_symmetry(root):
  Equal.cong(Pc.Note, List<Pc.Note>,
    z => Pc.transpose(3n, root) <> Pc.transpose(6n, root) <> Pc.transpose(9n, root) <> z <> Nil{},
    Pc.transpose(12n, root), root, transpose_period12(root))

# minor_ii_V_guide_tones: the second half is a plain {==} -- the iiø7's
# 7th is transpose(10, transpose(2, tonic)) and the V7's 3rd is
# transpose(4, transpose(7, tonic)), which succ takes to 12 half steps
# up from the tonic either way, and both sides share that normal form
# with no wraparound to reason about. The first half needs the same
# wraparound argument as tritone_sub_guide_tones: the V7's 7th is 7 +
# 10 == 17 half steps above the tonic, which transpose_add12 brings
# back to 5 -- the iiø7's 3rd, 2 + 3 half steps up.
def Laws.minor_ii_V_guide_tones(tonic):
  e1 = Laws.transpose_add(7n, 10n, tonic)
  # e1 : {Pc.transpose(10n, Pc.transpose(7n, tonic)) == Pc.transpose(17n, tonic) : Pc.Note}
  e2 = transpose_add12(5n, tonic)
  # e2 : {Pc.transpose(17n, tonic) == Pc.transpose(5n, tonic) : Pc.Note}
  common = Equal.trans(Pc.Note, Pc.transpose(10n, Pc.transpose(7n, tonic)), Pc.transpose(17n, tonic),
    Pc.transpose(5n, tonic), e1, e2)
  # common : {dom7_seventh(transpose(7, tonic)) == transpose(5, tonic) : Pc.Note}, and
  # min7b5_third(transpose(2, tonic)) *is* transpose(5, tonic) by unfolding
  (Equal.sym(Pc.Note, Pc.transpose(10n, Pc.transpose(7n, tonic)), Pc.transpose(5n, tonic), common), {==})
