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

# last_of
# -------

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

# Note/list equality
# -------------------
# solve_parallel's seam is now a value comparison (VL.select_result,
# via VL.list_note_eq), not a guess-then-verify, so the proof needs a
# soundness fact about that comparison: two note lists that compare
# list_note_eq really are the same list. Pc.Note is a closed
# 12-constructor enum with no arithmetic of its own; going through
# `index` and an explicit left inverse (`note_from_index`) turns
# "index(a) == index(b)" into "a == b" by congruence in 12 cases,
# instead of the 144 a head-on case split on both a and b would need.

def note_from_index(k: Nat) -> Pc.Note:
  match k:
    case 0n:
      Pc.C{}
    case 1n:
      Pc.Db{}
    case 2n:
      Pc.D{}
    case 3n:
      Pc.Eb{}
    case 4n:
      Pc.E{}
    case 5n:
      Pc.F{}
    case 6n:
      Pc.Gb{}
    case 7n:
      Pc.G{}
    case 8n:
      Pc.Ab{}
    case 9n:
      Pc.A{}
    case 10n:
      Pc.Bb{}
    case 11n:
      Pc.B{}
    case 1n+p:
      Pc.C{}

# note_from_index is a left inverse of index on every real note (the
# 1n+p catch-all above, for indices >= 12, never arises from index(n)
# itself, so it never needs a case here).
def note_from_index_index(n: Pc.Note) -> {note_from_index(Pc.index(n)) == n : Pc.Note}:
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

def pc_index_inj(+a: Pc.Note, +b: Pc.Note, e: {Pc.index(a) == Pc.index(b) : Nat}) -> {a == b : Pc.Note}:
  ca = note_from_index_index(a)
  cb = note_from_index_index(b)
  ce = Equal.cong(Nat, Pc.Note, note_from_index, Pc.index(a), Pc.index(b), e)
  # ce : note_from_index(index(a)) == note_from_index(index(b))
  step1 = Equal.trans(Pc.Note, a, note_from_index(Pc.index(a)), note_from_index(Pc.index(b)),
    Equal.sym(Pc.Note, note_from_index(Pc.index(a)), a, ca), ce)
  # step1 : a == note_from_index(index(b))
  Equal.trans(Pc.Note, a, note_from_index(Pc.index(b)), b, step1, cb)

def nat_is_eq_refl(k: Nat) -> {Nat.is_eq(k, k) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      nat_is_eq_refl(p)

def nat_is_eq_sound(x: Nat, y: Nat, e: {Nat.is_eq(x, y) == True{} : Bool}) -> {x == y : Nat}:
  match x:
    case 0n:
      match y:
        case 0n:
          {==}
        case 1n+q:
          Empty.absurd({0n == 1n+q : Nat}, false_ne_true(e))
    case 1n+p:
      match y:
        case 0n:
          Empty.absurd({1n+p == 0n : Nat}, false_ne_true(e))
        case 1n+q:
          %(nat_is_eq_sound(p, q, e)) : {1n+p == 1n+_ : Nat}
          {==}

def pc_is_eq_sound(+a: Pc.Note, +b: Pc.Note, e: {Pc.is_eq(a, b) == True{} : Bool}) -> {a == b : Pc.Note}:
  pc_index_inj(a, b, nat_is_eq_sound(Pc.index(a), Pc.index(b), e))

def pc_is_eq_refl(a: Pc.Note) -> {Pc.is_eq(a, a) == True{} : Bool}:
  nat_is_eq_refl(Pc.index(a))

# note-list discrimination (Nil vs Cons), the guide's motive technique
def note_list_disc(xs: +List<Pc.Note>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case h <> t:
      Empty

def nil_ne_cons_notes(h: Pc.Note, t: +List<Pc.Note>, e: {Nil{} == h <> t : +List<Pc.Note>}) -> Empty:
  %e : note_list_disc(_)
  Unit{}

def cons_ne_nil_notes(h: Pc.Note, t: +List<Pc.Note>, e: {h <> t == Nil{} : +List<Pc.Note>}) -> Empty:
  nil_ne_cons_notes(h, t, Equal.sym(+List<Pc.Note>, h <> t, Nil{}, e))

def list_note_eq_refl(xs: +List<Pc.Note>) -> {VL.list_note_eq(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      c1 = Equal.cong(Bool, Bool, z => z && VL.list_note_eq(t, t), Pc.is_eq(h, h), True{}, pc_is_eq_refl(h))
      c2 = Equal.cong(Bool, Bool, z => True{} && z, VL.list_note_eq(t, t), True{}, list_note_eq_refl(t))
      Equal.trans(Bool, Pc.is_eq(h, h) && VL.list_note_eq(t, t), True{} && VL.list_note_eq(t, t), True{}, c1, c2)

def list_note_eq_sound(xs: +List<Pc.Note>, ys: +List<Pc.Note>, +e: {VL.list_note_eq(xs, ys) == True{} : Bool}) ->
  {xs == ys : +List<Pc.Note>}:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          {==}
        case hy <> ty:
          Empty.absurd({Nil{} == hy <> ty : +List<Pc.Note>}, false_ne_true(e))
    case +hx <> +tx:
      match ys:
        case Nil{}:
          Empty.absurd({hx <> tx == Nil{} : +List<Pc.Note>}, false_ne_true(e))
        case +hy <> +ty:
          # e : {is_eq(hx,hy) && list_note_eq(tx,ty) == True{} : Bool}
          eh = and_true_l(Pc.is_eq(hx, hy), VL.list_note_eq(tx, ty), e)
          et = and_true_r(Pc.is_eq(hx, hy), VL.list_note_eq(tx, ty), e)
          ch = pc_is_eq_sound(hx, hy, eh)
          ct = list_note_eq_sound(tx, ty, et)
          c1 = Equal.cong(Pc.Note, +List<Pc.Note>, z => z <> tx, hx, hy, ch)
          c2 = Equal.cong(+List<Pc.Note>, +List<Pc.Note>, z => hy <> z, tx, ty, ct)
          Equal.trans(+List<Pc.Note>, hx <> tx, hy <> tx, hy <> ty, c1, c2)

# solve_chain_append: solve_chain is compositional
# ---------------------------------------------------
# solve_chain(xs++right, n, anchor) is exactly what you'd get by
# solving xs first and, if that succeeds, solving right from xs's own
# last voicing (or anchor, if xs is empty) and appending the two
# solutions -- a fact purely about solve_chain's own chord-by-chord
# recursion, with no mention of solve_parallel yet. This is the piece
# that makes solve_parallel's split provably lossless: it says what
# the *sequential* answer would be if you split it by hand.

def append_chords(xs: +List<Ch.Chord>, ys: +List<Ch.Chord>) -> +List<Ch.Chord>:
  match xs:
    case Nil{}:
      ys
    case c <> t:
      c <> append_chords(t, ys)

# identical in shape to VL.solve_parallel_finish (both: None -> None,
# Some{r} -> Some{append_sol(sol_left,r)}) -- reused directly below so
# that solve_parallel's own finish step and this reference combiner's
# are the *same* function, not two definitions that need a lemma to
# relate.
def solve_chain_combine(l: Maybe<&2, List<&2, +List<Pc.Note>>>, +right: +List<Ch.Chord>, +n: Nat,
  +anchor: +List<Pc.Note>) -> Maybe<&2, List<&2, +List<Pc.Note>>>:
  match l:
    case None{}:
      None{}
    case Some{+sol_left}:
      +real_anchor = VL.last_of(sol_left, anchor)
      VL.solve_parallel_finish(VL.solve_chain(right, n, real_anchor), sol_left)

def solve_chain_step_none_l(rest_sol: Maybe<&2, List<&2, +List<Pc.Note>>>) ->
  {VL.solve_chain_step(None{}, rest_sol) == None{} : Maybe<&2, List<&2, +List<Pc.Note>>>}:
  match rest_sol:
    case None{}:
      {==}
    case Some{vs}:
      {==}

# append_sol(Nil{},sol)==sol reduces on its own, but combine_finish
# still wraps a match around its first argument, so combine_finish(m,
# Nil{}) needs m's shape known before it collapses back to m itself.
def solve_parallel_finish_nil(m: Maybe<&2, List<&2, +List<Pc.Note>>>) ->
  {VL.solve_parallel_finish(m, Nil{}) == m : Maybe<&2, List<&2, +List<Pc.Note>>>}:
  match m:
    case None{}:
      {==}
    case Some{sol}:
      {==}

# transports an equation between two functions of a shared argument
# along an equality of that argument -- the same rewrite Equal.cong
# uses, generalized from one function to a difference of two.
def transport_eq2(-A: Type, -B: Type, -f: A -> B, -g: A -> B, -a: A, -b: A, e: {a == b : A},
  h: {f(a) == g(a) : B}) -> {f(b) == g(b) : B}:
  %e : {f(_) == g(_) : B}
  h

# solve_chain_step(Some{w}, combine_finish(x,sol_a)) == combine_finish(x, w<>sol_a),
# by cases on x alone -- append_sol(h<>t,ys)==h<>append_sol(t,ys) makes
# both sides reduce to the same cons once x's shape is known.
def solve_chain_step_combine_swap_at(x: Maybe<&2, List<&2, +List<Pc.Note>>>, sol_a: List<&2, +List<Pc.Note>>,
  w: +List<Pc.Note>) -> {VL.solve_chain_step(Some{w}, VL.solve_parallel_finish(x, sol_a)) ==
    VL.solve_parallel_finish(x, w <> sol_a) : Maybe<&2, List<&2, +List<Pc.Note>>>}:
  match x:
    case None{}:
      {==}
    case Some{sol_right}:
      {==}

# the Some{sol_a} case of solve_chain_step_combine_swap: reanchor via
# last_of_cons (last_of(w<>sol_a,anchor) == last_of(sol_a,w), so the
# right half is searched from the same voicing either way), then
# dispatch on that shared right-half result via the lemma above.
def solve_chain_step_combine_swap_some(+sol_a: List<&2, +List<Pc.Note>>, +w: +List<Pc.Note>, +right: +List<Ch.Chord>,
  +n: Nat, +anchor: +List<Pc.Note>) -> {VL.solve_chain_step(Some{w}, solve_chain_combine(Some{sol_a}, right, n, w)) ==
    solve_chain_combine(VL.solve_chain_step(Some{w}, Some{sol_a}), right, n, anchor) :
    Maybe<&2, List<&2, +List<Pc.Note>>>}:
  ec = last_of_cons(w, sol_a, anchor)
  # ec : {last_of(w<>sol_a,anchor) == last_of(sol_a,w) : +List<Pc.Note>}
  ecc = Equal.cong(+List<Pc.Note>, Maybe<&2, List<&2, +List<Pc.Note>>>, z => VL.solve_chain(right, n, z),
    VL.last_of(w <> sol_a, anchor), VL.last_of(sol_a, w), ec)
  step2 = Equal.cong(Maybe<&2, List<&2, +List<Pc.Note>>>, Maybe<&2, List<&2, +List<Pc.Note>>>,
    z => VL.solve_parallel_finish(z, w <> sol_a), VL.solve_chain(right, n, VL.last_of(w <> sol_a, anchor)),
    VL.solve_chain(right, n, VL.last_of(sol_a, w)), ecc)
  # step2 : {combine(Some{w<>sol_a},right,n,anchor) == combine_finish(X, w<>sol_a)} where X = solve_chain(right,n,last_of(sol_a,w))
  step3 = solve_chain_step_combine_swap_at(VL.solve_chain(right, n, VL.last_of(sol_a, w)), sol_a, w)
  # step3 : {solve_chain_step(Some{w}, combine(Some{sol_a},right,n,w)) == combine_finish(X, w<>sol_a)}
  Equal.trans(Maybe<&2, List<&2, +List<Pc.Note>>>,
    VL.solve_chain_step(Some{w}, solve_chain_combine(Some{sol_a}, right, n, w)),
    VL.solve_parallel_finish(VL.solve_chain(right, n, VL.last_of(sol_a, w)), w <> sol_a),
    solve_chain_combine(VL.solve_chain_step(Some{w}, Some{sol_a}), right, n, anchor),
    step3, Equal.sym(Maybe<&2, List<&2, +List<Pc.Note>>>,
      solve_chain_combine(VL.solve_chain_step(Some{w}, Some{sol_a}), right, n, anchor),
      VL.solve_parallel_finish(VL.solve_chain(right, n, VL.last_of(sol_a, w)), w <> sol_a), step2))

def solve_chain_step_combine_swap(a: Maybe<&2, List<&2, +List<Pc.Note>>>, w: +List<Pc.Note>, +right: +List<Ch.Chord>,
  +n: Nat, +anchor: +List<Pc.Note>) -> {VL.solve_chain_step(Some{w}, solve_chain_combine(a, right, n, w)) ==
    solve_chain_combine(VL.solve_chain_step(Some{w}, a), right, n, anchor) : Maybe<&2, List<&2, +List<Pc.Note>>>}:
  match a:
    case None{}:
      {==}
    case Some{sol_a}:
      solve_chain_step_combine_swap_some(sol_a, w, right, n, anchor)

def solve_chain_step_append_at(a: Maybe<&2, List<&2, +List<Pc.Note>>>, b: Maybe<&2, List<&2, +List<Pc.Note>>>,
  w: +List<Pc.Note>, +right: +List<Ch.Chord>, +n: Nat, +anchor: +List<Pc.Note>,
  ih: {b == solve_chain_combine(a, right, n, w) : Maybe<&2, List<&2, +List<Pc.Note>>>}) ->
  {VL.solve_chain_step(Some{w}, b) == solve_chain_combine(VL.solve_chain_step(Some{w}, a), right, n, anchor) :
    Maybe<&2, List<&2, +List<Pc.Note>>>}:
  step1 = Equal.cong(Maybe<&2, List<&2, +List<Pc.Note>>>, Maybe<&2, List<&2, +List<Pc.Note>>>,
    z => VL.solve_chain_step(Some{w}, z), b, solve_chain_combine(a, right, n, w), ih)
  step2 = solve_chain_step_combine_swap(a, w, right, n, anchor)
  Equal.trans(Maybe<&2, List<&2, +List<Pc.Note>>>, VL.solve_chain_step(Some{w}, b),
    VL.solve_chain_step(Some{w}, solve_chain_combine(a, right, n, w)),
    solve_chain_combine(VL.solve_chain_step(Some{w}, a), right, n, anchor), step1, step2)

# Some{w}: solve_chain_step(Some{w}, A) == None if A is None, Some{w<>a}
# if A is Some{a}. So the goal reduces to combining a match on the
# recursive `solve_chain(rest,n,w)` and `solve_chain(append_chords(rest,right),n,w)` --
# handled by cases on that recursive result (Maybe<voicing list>), via
# ih (the induction hypothesis, restated at anchor v = w by the caller).
def solve_chain_step_append_some(+w: +List<Pc.Note>, +rest: +List<Ch.Chord>, +right: +List<Ch.Chord>, +n: Nat,
  +anchor: +List<Pc.Note>,
  ih: {VL.solve_chain(append_chords(rest, right), n, w) ==
    solve_chain_combine(VL.solve_chain(rest, n, w), right, n, w) : Maybe<&2, List<&2, +List<Pc.Note>>>}) ->
  {VL.solve_chain_step(Some{w}, VL.solve_chain(append_chords(rest, right), n, w)) ==
    solve_chain_combine(VL.solve_chain_step(Some{w}, VL.solve_chain(rest, n, w)), right, n, anchor) :
    Maybe<&2, List<&2, +List<Pc.Note>>>}:
  solve_chain_step_append_at(VL.solve_chain(rest, n, w), VL.solve_chain(append_chords(rest, right), n, w),
    w, right, n, anchor, ih)

# solve_chain_step_append: the step case of solve_chain_append, with
# `chosen` (the current chord's search result) taken as an explicit
# parameter so it can be matched -- mirrors solve_chain_step_bounded's
# own dispatch, but concludes an equality of results, not a bound.
def solve_chain_step_append(chosen: Maybe<&2, +List<Pc.Note>>, +v: +List<Pc.Note>, +rest: +List<Ch.Chord>,
  +right: +List<Ch.Chord>, +n: Nat, +anchor: +List<Pc.Note>,
  hv: @w: +List<Pc.Note> -> {chosen == Some{w} : Maybe<&2, +List<Pc.Note>>} -> {v == w : +List<Pc.Note>},
  ih: {VL.solve_chain(append_chords(rest, right), n, v) ==
    solve_chain_combine(VL.solve_chain(rest, n, v), right, n, v) : Maybe<&2, List<&2, +List<Pc.Note>>>}) ->
  {VL.solve_chain_step(chosen, VL.solve_chain(append_chords(rest, right), n, v)) ==
    solve_chain_combine(VL.solve_chain_step(chosen, VL.solve_chain(rest, n, v)), right, n, anchor) :
    Maybe<&2, List<&2, +List<Pc.Note>>>}:
  match chosen:
    case None{}:
      c1 = solve_chain_step_none_l(VL.solve_chain(append_chords(rest, right), n, v))
      c2 = solve_chain_step_none_l(VL.solve_chain(rest, n, v))
      c2c = Equal.cong(Maybe<&2, List<&2, +List<Pc.Note>>>, Maybe<&2, List<&2, +List<Pc.Note>>>,
        z => solve_chain_combine(z, right, n, anchor), VL.solve_chain_step(None{}, VL.solve_chain(rest, n, v)),
        None{}, c2)
      # c2c : {solve_chain_combine(solve_chain_step(None,solve_chain(rest,n,v)),right,n,anchor) ==
      #        solve_chain_combine(None{},right,n,anchor) : Maybe<...>}
      Equal.trans(Maybe<&2, List<&2, +List<Pc.Note>>>, VL.solve_chain_step(None{}, VL.solve_chain(append_chords(rest, right), n, v)),
        None{}, solve_chain_combine(VL.solve_chain_step(None{}, VL.solve_chain(rest, n, v)), right, n, anchor),
        c1, Equal.sym(Maybe<&2, List<&2, +List<Pc.Note>>>,
          solve_chain_combine(VL.solve_chain_step(None{}, VL.solve_chain(rest, n, v)), right, n, anchor),
          solve_chain_combine(None{}, right, n, anchor), c2c))
    case Some{+w}:
      +ev = hv(w, {==})
      # ev : {v == w : +List<Pc.Note>}
      ih_w = transport_eq2(+List<Pc.Note>, Maybe<&2, List<&2, +List<Pc.Note>>>,
        z => VL.solve_chain(append_chords(rest, right), n, z),
        z => solve_chain_combine(VL.solve_chain(rest, n, z), right, n, z), v, w, ev, ih)
      result_w = solve_chain_step_append_some(w, rest, right, n, anchor, ih_w)
      transport_eq2(+List<Pc.Note>, Maybe<&2, List<&2, +List<Pc.Note>>>,
        z => VL.solve_chain_step(Some{w}, VL.solve_chain(append_chords(rest, right), n, z)),
        z => solve_chain_combine(VL.solve_chain_step(Some{w}, VL.solve_chain(rest, n, z)), right, n, anchor),
        w, v, Equal.sym(+List<Pc.Note>, v, w, ev), result_w)

def solve_chain_append(xs: +List<Ch.Chord>, +right: +List<Ch.Chord>, +n: Nat, +anchor: +List<Pc.Note>) ->
  {VL.solve_chain(append_chords(xs, right), n, anchor) ==
    solve_chain_combine(VL.solve_chain(xs, n, anchor), right, n, anchor) : Maybe<&2, List<&2, +List<Pc.Note>>>}:
  match xs:
    case Nil{}:
      Equal.sym(Maybe<&2, List<&2, +List<Pc.Note>>>, VL.solve_parallel_finish(VL.solve_chain(right, n, anchor), Nil{}),
        VL.solve_chain(right, n, anchor), solve_parallel_finish_nil(VL.solve_chain(right, n, anchor)))
    case c <> +rest:
      +chosen = VL.search(VL.candidates(c), anchor, n)
      +v = VL.from_maybe_v(chosen, Nil{})
      solve_chain_step_append(chosen, v, rest, right, n, anchor,
        w => e2 => from_maybe_some(chosen, Nil{}, w, e2),
        solve_chain_append(rest, right, n, v))

# split_at_append: splitting a progression and appending the two
# halves back together is the identity -- the fact that lets
# solve_chain_append apply to solve_parallel's own split.
def append_chords_pair(pair: +List<Ch.Chord> & +List<Ch.Chord>) -> +List<Ch.Chord>:
  match pair:
    case (l, r):
      append_chords(l, r)

def split_cons_append(c: Ch.Chord, pair: +List<Ch.Chord> & +List<Ch.Chord>, t: +List<Ch.Chord>,
  ih: {append_chords_pair(pair) == t : +List<Ch.Chord>}) ->
  {append_chords_pair(VL.split_cons(c, pair)) == c <> t : +List<Ch.Chord>}:
  match pair:
    case (l, r):
      Equal.cong(+List<Ch.Chord>, +List<Ch.Chord>, z => c <> z, append_chords(l, r), t, ih)

def split_at_append(k: Nat, xs: +List<Ch.Chord>) -> {append_chords_pair(VL.split_at(k, xs)) == xs : +List<Ch.Chord>}:
  match k xs:
    case 0n Nil{}:
      {==}
    case 0n c <> +t:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+ +p c <> +t:
      split_cons_append(c, VL.split_at(p, t), t, split_at_append(p, t))

# select_result agreement with search
# --------------------------------------
# The candidate-selection machinery agrees with search itself: on the
# one call path that ever matters (right_results built by
# solve_from_each_anchor over the very candidate list search walked),
# select_result recovers exactly the same result solve_chain would
# have computed directly from search's own chosen voicing. No re-run
# of search and no value comparison against "the real answer" is
# needed elsewhere -- this is the one place the seam's correctness
# reduces to.

def select_result_pick_true(b: Bool, r: Maybe<&2, List<&2, +List<Pc.Note>>>,
  rest: Maybe<&2, List<&2, +List<Pc.Note>>>, e: {b == True{} : Bool}) ->
  {VL.select_result_pick(b, r, rest) == r : Maybe<&2, List<&2, +List<Pc.Note>>>}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({VL.select_result_pick(b, r, rest) == r : Maybe<&2, List<&2, +List<Pc.Note>>>}, false_ne_true(e))

# dispatches select_result_pick(b2, solve_chain(right,n,h), rest) to
# solve_chain(right,n,w), given rest already equals it: if b2 is True,
# w and h coincide by value (list_note_eq_sound) so solve_chain(right,
# n,h) is the same call; if False, rest's own equality (ihw) closes it.
def select_result_pick_dispatch(b2: Bool, h: +List<Pc.Note>, w: +List<Pc.Note>, +right: +List<Ch.Chord>, +n: Nat,
  rest: Maybe<&2, List<&2, +List<Pc.Note>>>,
  vbe2: {VL.list_note_eq(w, h) == b2 : Bool},
  ihw: {rest == VL.solve_chain(right, n, w) : Maybe<&2, List<&2, +List<Pc.Note>>>}) ->
  {VL.select_result_pick(b2, VL.solve_chain(right, n, h), rest) == VL.solve_chain(right, n, w) :
    Maybe<&2, List<&2, +List<Pc.Note>>>}:
  match b2:
    case True{}:
      hw = list_note_eq_sound(w, h, vbe2)
      # hw : {w == h : +List<Pc.Note>}
      Equal.sym(Maybe<&2, List<&2, +List<Pc.Note>>>, VL.solve_chain(right, n, w), VL.solve_chain(right, n, h),
        Equal.cong(+List<Pc.Note>, Maybe<&2, List<&2, +List<Pc.Note>>>, z => VL.solve_chain(right, n, z), w, h, hw))
    case False{}:
      ihw

def search_select_agree_pick(b: Bool, +h: +List<Pc.Note>, +t: List<&2, +List<Pc.Note>>, +right: +List<Ch.Chord>,
  +n: Nat, +anchor: +List<Pc.Note>, +w: +List<Pc.Note>,
  vbe: {VL.voices_bounded(anchor, h, n) == b : Bool},
  e: {VL.search_pick(b, h, VL.search(t, anchor, n)) == Some{w} : Maybe<&2, +List<Pc.Note>>},
  ih: @w2: +List<Pc.Note> -> {VL.search(t, anchor, n) == Some{w2} : Maybe<&2, +List<Pc.Note>>} ->
    {VL.select_result(t, VL.solve_from_each_anchor(t, right, n), w2) == VL.solve_chain(right, n, w2) :
      Maybe<&2, List<&2, +List<Pc.Note>>>}) ->
  {VL.select_result(h <> t, VL.solve_from_each_anchor(h <> t, right, n), w) == VL.solve_chain(right, n, w) :
    Maybe<&2, List<&2, +List<Pc.Note>>>}:
  match b:
    case True{}:
      +ew = some_inj(+List<Pc.Note>, h, w, e)
      # ew : {h == w : +List<Pc.Note>}
      lwb = Equal.trans(Bool, VL.list_note_eq(w, h), VL.list_note_eq(h, h), True{},
        Equal.cong(+List<Pc.Note>, Bool, z => VL.list_note_eq(z, h), w, h, Equal.sym(+List<Pc.Note>, h, w, ew)),
        list_note_eq_refl(h))
      # lwb : {list_note_eq(w,h) == True{} : Bool}
      sp = select_result_pick_true(VL.list_note_eq(w, h), VL.solve_chain(right, n, h),
        VL.select_result(t, VL.solve_from_each_anchor(t, right, n), w), lwb)
      # sp : {select_result_pick(list_note_eq(w,h), solve_chain(right,n,h), ...) == solve_chain(right,n,h)}
      Equal.trans(Maybe<&2, List<&2, +List<Pc.Note>>>,
        VL.select_result_pick(VL.list_note_eq(w, h), VL.solve_chain(right, n, h),
          VL.select_result(t, VL.solve_from_each_anchor(t, right, n), w)),
        VL.solve_chain(right, n, h), VL.solve_chain(right, n, w), sp,
        Equal.cong(+List<Pc.Note>, Maybe<&2, List<&2, +List<Pc.Note>>>, z => VL.solve_chain(right, n, z), h, w, ew))
    case False{}:
      ihw = ih(w, e)
      # ihw : {select_result(t, solve_from_each_anchor(t,right,n), w) == solve_chain(right,n,w)}
      select_result_pick_dispatch(VL.list_note_eq(w, h), h, w, right, n,
        VL.select_result(t, VL.solve_from_each_anchor(t, right, n), w), {==}, ihw)

def search_select_agree(cs: List<&2, +List<Pc.Note>>, +right: +List<Ch.Chord>, +n: Nat, +anchor: +List<Pc.Note>,
  w: +List<Pc.Note>, e: {VL.search(cs, anchor, n) == Some{w} : Maybe<&2, +List<Pc.Note>>}) ->
  {VL.select_result(cs, VL.solve_from_each_anchor(cs, right, n), w) == VL.solve_chain(right, n, w) :
    Maybe<&2, List<&2, +List<Pc.Note>>>}:
  match cs:
    case Nil{}:
      Empty.absurd({VL.select_result(cs, VL.solve_from_each_anchor(cs, right, n), w) == VL.solve_chain(right, n, w) :
        Maybe<&2, List<&2, +List<Pc.Note>>>}, none_ne_some(+List<Pc.Note>, w, e))
    case +h <> +t:
      search_select_agree_pick(VL.voices_bounded(anchor, h, n), h, t, right, n, anchor, w, {==}, e,
        w2 => e2 => search_select_agree(t, right, n, anchor, w2, e2))

# solve_chain_left_selects_right
# ---------------------------------
# The main seam lemma: whenever solve_chain solves a left half `xs`
# from `anchor`, picking the right-half result out of
# solve_from_each_anchor's precomputed list -- by the left half's own
# real last voicing -- gives exactly what solve_chain would have
# computed for the right half directly from that voicing. This is
# what makes the selection in solve_parallel_combine a genuine
# replacement for running the right half sequentially, rather than a
# guess: combined with solve_chain_append it shows the split-and-
# select design computes the same thing solve_chain does in one pass.

# a nonempty chord list's last chord always exists -- CPS-style (a
# continuation taking the witness and its proof) rather than returning
# a dependent pair, so callers never need to destructure a computed
# value.
def last_chord_some(-A: Type, t: +List<Ch.Chord>, c: Ch.Chord,
  k: @w: Ch.Chord -> {VL.last_chord(c <> t) == Some{w} : Maybe<&2, Ch.Chord>} -> A) -> A:
  match t:
    case Nil{}:
      k(c, {==})
    case c2 <> t2:
      last_chord_some(A, t2, c2, k)

# pick_anchor_list ignores its anchor argument once the chord is known
# (Some{w}): both sides reduce to candidates(w) regardless of a or b.
def pick_anchor_list_indep(w: Ch.Chord, +a: +List<Pc.Note>, +b: +List<Pc.Note>) ->
  {VL.pick_anchor_list(Some{w}, a) == VL.pick_anchor_list(Some{w}, b) : List<&2, +List<Pc.Note>>}:
  {==}

# xs = [c]: solve_chain([c],n,anchor) = solve_chain_step(chosen, Some{Nil{}}),
# so it only succeeds (chosen = Some{w}) with sol = [w]; last_of([w],anchor)
# = w, last_chord([c]) = Some{c}, and search_select_agree closes it.
def case_last_chord(c: Ch.Chord, chosen: Maybe<&2, +List<Pc.Note>>, +right: +List<Ch.Chord>, +n: Nat,
  +anchor: +List<Pc.Note>, sol: List<&2, +List<Pc.Note>>,
  e: {VL.solve_chain_step(chosen, VL.solve_chain(Nil{}, n, VL.from_maybe_v(chosen, Nil{}))) == Some{sol} :
    Maybe<&2, List<&2, +List<Pc.Note>>>},
  hb: @w2: +List<Pc.Note> -> {chosen == Some{w2} : Maybe<&2, +List<Pc.Note>>} ->
    {VL.search(VL.candidates(c), anchor, n) == Some{w2} : Maybe<&2, +List<Pc.Note>>}) ->
  {VL.select_result(VL.pick_anchor_list(Some{c}, anchor),
    VL.solve_from_each_anchor(VL.pick_anchor_list(Some{c}, anchor), right, n), VL.last_of(sol, anchor)) ==
    VL.solve_chain(right, n, VL.last_of(sol, anchor)) : Maybe<&2, List<&2, +List<Pc.Note>>>}:
  match chosen:
    case None{}:
      Empty.absurd({VL.select_result(VL.pick_anchor_list(Some{c}, anchor),
        VL.solve_from_each_anchor(VL.pick_anchor_list(Some{c}, anchor), right, n), VL.last_of(sol, anchor)) ==
        VL.solve_chain(right, n, VL.last_of(sol, anchor)) : Maybe<&2, List<&2, +List<Pc.Note>>>},
        none_ne_some(List<&2, +List<Pc.Note>>, sol, e))
    case Some{+w}:
      +es = some_inj(List<&2, +List<Pc.Note>>, w <> Nil{}, sol, e)
      # es : {w<>Nil{} == sol : List<&2, +List<Pc.Note>>}
      agree = search_select_agree(VL.candidates(c), right, n, anchor, w, hb(w, {==}))
      # agree : {select_result(candidates(c), solve_from_each_anchor(candidates(c),right,n), w) == solve_chain(right,n,w)}
      %es : {VL.select_result(VL.pick_anchor_list(Some{c}, anchor),
        VL.solve_from_each_anchor(VL.pick_anchor_list(Some{c}, anchor), right, n), VL.last_of(_, anchor)) ==
        VL.solve_chain(right, n, VL.last_of(_, anchor)) : Maybe<&2, List<&2, +List<Pc.Note>>>}
      agree

# last_chord_some(c2,t2) is a computed value, so its witness pair
# is destructured here, where it is a genuine parameter, not inline
# at the call site.
def case_mid_chord_finish(c2: Ch.Chord, t2: +List<Ch.Chord>, w: +List<Pc.Note>, +right: +List<Ch.Chord>, +n: Nat,
  +anchor: +List<Pc.Note>, +vs: List<&2, +List<Pc.Note>>, sol: List<&2, +List<Pc.Note>>,
  es: {w <> vs == sol : List<&2, +List<Pc.Note>>},
  eloc: {VL.last_of(w <> vs, anchor) == VL.last_of(vs, w) : +List<Pc.Note>},
  ih: {VL.select_result(VL.pick_anchor_list(VL.last_chord(c2 <> t2), w),
    VL.solve_from_each_anchor(VL.pick_anchor_list(VL.last_chord(c2 <> t2), w), right, n), VL.last_of(vs, w)) ==
    VL.solve_chain(right, n, VL.last_of(vs, w)) : Maybe<&2, List<&2, +List<Pc.Note>>>},
  w0: Ch.Chord, +ew0: {VL.last_chord(c2 <> t2) == Some{w0} : Maybe<&2, Ch.Chord>}) ->
  {VL.select_result(VL.pick_anchor_list(VL.last_chord(c2 <> t2), anchor),
    VL.solve_from_each_anchor(VL.pick_anchor_list(VL.last_chord(c2 <> t2), anchor), right, n),
    VL.last_of(sol, anchor)) == VL.solve_chain(right, n, VL.last_of(sol, anchor)) :
    Maybe<&2, List<&2, +List<Pc.Note>>>}:
      +indep = pick_anchor_list_indep(w0, w, anchor)
      # indep : {pick_anchor_list(Some{w0},w) == pick_anchor_list(Some{w0},anchor)}
      al_eq = Equal.trans(List<&2, +List<Pc.Note>>, VL.pick_anchor_list(VL.last_chord(c2 <> t2), w),
        VL.pick_anchor_list(Some{w0}, w), VL.pick_anchor_list(VL.last_chord(c2 <> t2), anchor),
        Equal.cong(Maybe<&2, Ch.Chord>, List<&2, +List<Pc.Note>>, m => VL.pick_anchor_list(m, w),
          VL.last_chord(c2 <> t2), Some{w0}, ew0),
        Equal.trans(List<&2, +List<Pc.Note>>, VL.pick_anchor_list(Some{w0}, w), VL.pick_anchor_list(Some{w0}, anchor),
          VL.pick_anchor_list(VL.last_chord(c2 <> t2), anchor), indep,
          Equal.sym(List<&2, +List<Pc.Note>>, VL.pick_anchor_list(VL.last_chord(c2 <> t2), anchor),
            VL.pick_anchor_list(Some{w0}, anchor),
            Equal.cong(Maybe<&2, Ch.Chord>, List<&2, +List<Pc.Note>>, m => VL.pick_anchor_list(m, anchor),
              VL.last_chord(c2 <> t2), Some{w0}, ew0))))
      # al_eq : {pick_anchor_list(last_chord(c2<>t2),w) == pick_anchor_list(last_chord(c2<>t2),anchor)}
      cong_al = Equal.cong(List<&2, +List<Pc.Note>>, Maybe<&2, List<&2, +List<Pc.Note>>>,
        z => VL.select_result(z, VL.solve_from_each_anchor(z, right, n), VL.last_of(vs, w)),
        VL.pick_anchor_list(VL.last_chord(c2 <> t2), w), VL.pick_anchor_list(VL.last_chord(c2 <> t2), anchor), al_eq)
      # cong_al : {select_result(AL_w, ..., last_of(vs,w)) == select_result(AL_anchor, ..., last_of(vs,w))}
      final_w = Equal.trans(Maybe<&2, List<&2, +List<Pc.Note>>>,
        VL.select_result(VL.pick_anchor_list(VL.last_chord(c2 <> t2), anchor),
          VL.solve_from_each_anchor(VL.pick_anchor_list(VL.last_chord(c2 <> t2), anchor), right, n),
          VL.last_of(vs, w)),
        VL.select_result(VL.pick_anchor_list(VL.last_chord(c2 <> t2), w),
          VL.solve_from_each_anchor(VL.pick_anchor_list(VL.last_chord(c2 <> t2), w), right, n), VL.last_of(vs, w)),
        VL.solve_chain(right, n, VL.last_of(vs, w)), Equal.sym(Maybe<&2, List<&2, +List<Pc.Note>>>,
          VL.select_result(VL.pick_anchor_list(VL.last_chord(c2 <> t2), w),
            VL.solve_from_each_anchor(VL.pick_anchor_list(VL.last_chord(c2 <> t2), w), right, n), VL.last_of(vs, w)),
          VL.select_result(VL.pick_anchor_list(VL.last_chord(c2 <> t2), anchor),
            VL.solve_from_each_anchor(VL.pick_anchor_list(VL.last_chord(c2 <> t2), anchor), right, n),
            VL.last_of(vs, w)), cong_al), ih)
      # final_w : {select_result(pick_anchor_list(last_chord(c2<>t2),anchor), ..., last_of(vs,w)) == solve_chain(right,n,last_of(vs,w))}
      %es : {VL.select_result(VL.pick_anchor_list(VL.last_chord(c2 <> t2), anchor),
        VL.solve_from_each_anchor(VL.pick_anchor_list(VL.last_chord(c2 <> t2), anchor), right, n),
        VL.last_of(_, anchor)) == VL.solve_chain(right, n, VL.last_of(_, anchor)) :
        Maybe<&2, List<&2, +List<Pc.Note>>>}
      %(Equal.sym(+List<Pc.Note>, VL.last_of(w <> vs, anchor), VL.last_of(vs, w), eloc)) :
        {VL.select_result(VL.pick_anchor_list(VL.last_chord(c2 <> t2), anchor),
          VL.solve_from_each_anchor(VL.pick_anchor_list(VL.last_chord(c2 <> t2), anchor), right, n), _) ==
          VL.solve_chain(right, n, _) : Maybe<&2, List<&2, +List<Pc.Note>>>}
      final_w

def case_mid_chord_at(+c2: Ch.Chord, +t2: +List<Ch.Chord>, +w: +List<Pc.Note>, +right: +List<Ch.Chord>, +n: Nat,
  +anchor: +List<Pc.Note>, rest_res: Maybe<&2, List<&2, +List<Pc.Note>>>, +sol: List<&2, +List<Pc.Note>>,
  ers: {VL.solve_chain(c2 <> t2, n, w) == rest_res : Maybe<&2, List<&2, +List<Pc.Note>>>},
  e: {VL.solve_chain_step(Some{w}, rest_res) == Some{sol} : Maybe<&2, List<&2, +List<Pc.Note>>>},
  ih_provider: @vs2: List<&2, +List<Pc.Note>> -> {VL.solve_chain(c2 <> t2, n, w) == Some{vs2} :
    Maybe<&2, List<&2, +List<Pc.Note>>>} -> {VL.select_result(VL.pick_anchor_list(VL.last_chord(c2 <> t2), w),
    VL.solve_from_each_anchor(VL.pick_anchor_list(VL.last_chord(c2 <> t2), w), right, n), VL.last_of(vs2, w)) ==
    VL.solve_chain(right, n, VL.last_of(vs2, w)) : Maybe<&2, List<&2, +List<Pc.Note>>>}) ->
  {VL.select_result(VL.pick_anchor_list(VL.last_chord(c2 <> t2), anchor),
    VL.solve_from_each_anchor(VL.pick_anchor_list(VL.last_chord(c2 <> t2), anchor), right, n),
    VL.last_of(sol, anchor)) == VL.solve_chain(right, n, VL.last_of(sol, anchor)) :
    Maybe<&2, List<&2, +List<Pc.Note>>>}:
  match rest_res:
    case None{}:
      Empty.absurd({VL.select_result(VL.pick_anchor_list(VL.last_chord(c2 <> t2), anchor),
        VL.solve_from_each_anchor(VL.pick_anchor_list(VL.last_chord(c2 <> t2), anchor), right, n),
        VL.last_of(sol, anchor)) == VL.solve_chain(right, n, VL.last_of(sol, anchor)) :
        Maybe<&2, List<&2, +List<Pc.Note>>>}, none_ne_some(List<&2, +List<Pc.Note>>, sol, e))
    case Some{+vs}:
      +es = some_inj(List<&2, +List<Pc.Note>>, w <> vs, sol, e)
      # es : {w<>vs == sol : List<&2, +List<Pc.Note>>}
      +eloc = last_of_cons(w, vs, anchor)
      # eloc : {last_of(w<>vs,anchor) == last_of(vs,w) : +List<Pc.Note>}
      ih = ih_provider(vs, ers)
      last_chord_some({VL.select_result(VL.pick_anchor_list(VL.last_chord(c2 <> t2), anchor),
          VL.solve_from_each_anchor(VL.pick_anchor_list(VL.last_chord(c2 <> t2), anchor), right, n),
          VL.last_of(sol, anchor)) == VL.solve_chain(right, n, VL.last_of(sol, anchor)) :
          Maybe<&2, List<&2, +List<Pc.Note>>>}, t2, c2,
        w0 => ew0 => case_mid_chord_finish(c2, t2, w, right, n, anchor, vs, sol, es, eloc, ih, w0, ew0))

# xs = c<>(c2<>t2): reanchor last_chord(c2<>t2)'s candidate list from
# the intermediate voicing w onto the outer anchor (pick_anchor_list_indep,
# using the witness that a nonempty tail always has a last chord), then
# apply the induction hypothesis at w. ih_provider is the recursive
# call, supplied by solve_chain_left_selects_right itself (as a
# closure) so this function never calls it by name -- avoiding the
# mutual recursion Bend forbids between separately named defs.
def case_mid_chord(c: Ch.Chord, +c2: Ch.Chord, +t2: +List<Ch.Chord>, chosen: Maybe<&2, +List<Pc.Note>>,
  +right: +List<Ch.Chord>, +n: Nat, +anchor: +List<Pc.Note>, sol: List<&2, +List<Pc.Note>>,
  e: {VL.solve_chain_step(chosen, VL.solve_chain(c2 <> t2, n, VL.from_maybe_v(chosen, Nil{}))) == Some{sol} :
    Maybe<&2, List<&2, +List<Pc.Note>>>},
  ih_provider: @w2: +List<Pc.Note> -> @vs2: List<&2, +List<Pc.Note>> ->
    {VL.solve_chain(c2 <> t2, n, w2) == Some{vs2} : Maybe<&2, List<&2, +List<Pc.Note>>>} ->
    {VL.select_result(VL.pick_anchor_list(VL.last_chord(c2 <> t2), w2),
      VL.solve_from_each_anchor(VL.pick_anchor_list(VL.last_chord(c2 <> t2), w2), right, n), VL.last_of(vs2, w2)) ==
      VL.solve_chain(right, n, VL.last_of(vs2, w2)) : Maybe<&2, List<&2, +List<Pc.Note>>>}) ->
  {VL.select_result(VL.pick_anchor_list(VL.last_chord(c2 <> t2), anchor),
    VL.solve_from_each_anchor(VL.pick_anchor_list(VL.last_chord(c2 <> t2), anchor), right, n),
    VL.last_of(sol, anchor)) == VL.solve_chain(right, n, VL.last_of(sol, anchor)) :
    Maybe<&2, List<&2, +List<Pc.Note>>>}:
  match chosen:
    case None{}:
      none_e = solve_chain_step_none_l(VL.solve_chain(c2 <> t2, n, VL.from_maybe_v(None{}, Nil{})))
      # none_e : {solve_chain_step(None{}, solve_chain(c2<>t2,n,Nil{})) == None{} : Maybe<...>}
      e2 = Equal.trans(Maybe<&2, List<&2, +List<Pc.Note>>>, None{},
        VL.solve_chain_step(None{}, VL.solve_chain(c2 <> t2, n, VL.from_maybe_v(None{}, Nil{}))), Some{sol},
        Equal.sym(Maybe<&2, List<&2, +List<Pc.Note>>>,
          VL.solve_chain_step(None{}, VL.solve_chain(c2 <> t2, n, VL.from_maybe_v(None{}, Nil{}))), None{}, none_e), e)
      Empty.absurd({VL.select_result(VL.pick_anchor_list(VL.last_chord(c2 <> t2), anchor),
        VL.solve_from_each_anchor(VL.pick_anchor_list(VL.last_chord(c2 <> t2), anchor), right, n),
        VL.last_of(sol, anchor)) == VL.solve_chain(right, n, VL.last_of(sol, anchor)) :
        Maybe<&2, List<&2, +List<Pc.Note>>>}, none_ne_some(List<&2, +List<Pc.Note>>, sol, e2))
    case Some{+w}:
      case_mid_chord_at(c2, t2, w, right, n, anchor, VL.solve_chain(c2 <> t2, n, w), sol, {==}, e,
        ih_provider(w))

def solve_chain_left_selects_right(xs: +List<Ch.Chord>, +right: +List<Ch.Chord>, +n: Nat, +anchor: +List<Pc.Note>,
  sol: List<&2, +List<Pc.Note>>,
  e: {VL.solve_chain(xs, n, anchor) == Some{sol} : Maybe<&2, List<&2, +List<Pc.Note>>>}) ->
  {VL.select_result(VL.pick_anchor_list(VL.last_chord(xs), anchor),
    VL.solve_from_each_anchor(VL.pick_anchor_list(VL.last_chord(xs), anchor), right, n),
    VL.last_of(sol, anchor)) == VL.solve_chain(right, n, VL.last_of(sol, anchor)) :
    Maybe<&2, List<&2, +List<Pc.Note>>>}:
  match xs:
    case Nil{}:
      +es = some_inj(List<&2, +List<Pc.Note>>, Nil{}, sol, e)
      # es : {Nil{} == sol : List<&2, +List<Pc.Note>>}
      sp = select_result_pick_true(VL.list_note_eq(anchor, anchor), VL.solve_chain(right, n, anchor), None{},
        list_note_eq_refl(anchor))
      # sp : {select_result_pick(list_note_eq(anchor,anchor), solve_chain(right,n,anchor), None{}) == solve_chain(right,n,anchor)}
      base = Equal.trans(Maybe<&2, List<&2, +List<Pc.Note>>>,
        VL.select_result_pick(VL.list_note_eq(anchor, anchor), VL.solve_chain(right, n, anchor), None{}),
        VL.solve_chain(right, n, anchor), VL.solve_chain(right, n, anchor), sp, {==})
      # base : {select_result(anchor<>Nil{}, solve_chain(right,n,anchor)<>Nil{}, anchor) == solve_chain(right,n,anchor)}
      %es : {VL.select_result(VL.pick_anchor_list(VL.last_chord(Nil{}), anchor),
        VL.solve_from_each_anchor(VL.pick_anchor_list(VL.last_chord(Nil{}), anchor), right, n),
        VL.last_of(_, anchor)) == VL.solve_chain(right, n, VL.last_of(_, anchor)) :
        Maybe<&2, List<&2, +List<Pc.Note>>>}
      base
    case +c <> t:
      match t:
        case Nil{}:
          +chosen = VL.search(VL.candidates(c), anchor, n)
          case_last_chord(c, chosen, right, n, anchor, sol, e, w2 => e2 => e2)
        case +c2 <> +t2:
          +chosen = VL.search(VL.candidates(c), anchor, n)
          case_mid_chord(c, c2, t2, chosen, right, n, anchor, sol, e,
            w2 => vs2 => e2 => solve_chain_left_selects_right(c2 <> t2, right, n, w2, vs2, e2))

# solve_parallel_eq_solve_chain
# --------------------------------
# solve_parallel_combine (voicelead.bend) and solve_chain_combine
# (above) are the same shape one level up: both dispatch on a Maybe
# solution and finish with VL.solve_parallel_finish, one selecting the
# right-half result from the precomputed list, the other calling
# solve_chain directly. solve_chain_left_selects_right is exactly the
# fact that those two right-half values agree, so this lemma lifts it
# from "one Maybe" to "solve_parallel_split's whole computation".

def solve_parallel_combine_eq(l: Maybe<&2, List<&2, +List<Pc.Note>>>, +left: +List<Ch.Chord>,
  +right: +List<Ch.Chord>, +n: Nat, +anchor: +List<Pc.Note>,
  el: {VL.solve_chain(left, n, anchor) == l : Maybe<&2, List<&2, +List<Pc.Note>>>}) ->
  {VL.solve_parallel_combine(l, VL.solve_from_each_anchor(VL.pick_anchor_list(VL.last_chord(left), anchor), right, n),
    VL.pick_anchor_list(VL.last_chord(left), anchor), anchor) == solve_chain_combine(l, right, n, anchor) :
    Maybe<&2, List<&2, +List<Pc.Note>>>}:
  match l:
    case None{}:
      {==}
    case Some{+sol_left}:
      +real_anchor = VL.last_of(sol_left, anchor)
      +e_sel = solve_chain_left_selects_right(left, right, n, anchor, sol_left, el)
      # e_sel : {select_result(pick_anchor_list(last_chord(left),anchor),
      #            solve_from_each_anchor(pick_anchor_list(last_chord(left),anchor),right,n), real_anchor)
      #          == solve_chain(right,n,real_anchor)}
      Equal.cong(Maybe<&2, List<&2, +List<Pc.Note>>>, Maybe<&2, List<&2, +List<Pc.Note>>>,
        z => VL.solve_parallel_finish(z, sol_left),
        VL.select_result(VL.pick_anchor_list(VL.last_chord(left), anchor),
          VL.solve_from_each_anchor(VL.pick_anchor_list(VL.last_chord(left), anchor), right, n), real_anchor),
        VL.solve_chain(right, n, real_anchor), e_sel)

def solve_parallel_split_eq(pair: +List<Ch.Chord> & +List<Ch.Chord>, +n: Nat, +anchor: +List<Pc.Note>,
  +chords: +List<Ch.Chord>, eapp: {append_chords_pair(pair) == chords : +List<Ch.Chord>}) ->
  {VL.solve_parallel_split(pair, n, anchor) == VL.solve_chain(chords, n, anchor) : Maybe<&2, List<&2, +List<Pc.Note>>>}:
  match pair:
    case (+left, +right):
      +combined = solve_parallel_combine_eq(VL.solve_chain(left, n, anchor), left, right, n, anchor, {==})
      # combined : {solve_parallel_split((left,right),n,anchor) == solve_chain_combine(solve_chain(left,n,anchor),right,n,anchor)}
      +sc_append = solve_chain_append(left, right, n, anchor)
      # sc_append : {solve_chain(append_chords(left,right),n,anchor) == solve_chain_combine(solve_chain(left,n,anchor),right,n,anchor)}
      step = Equal.trans(Maybe<&2, List<&2, +List<Pc.Note>>>, VL.solve_parallel_split((left, right), n, anchor),
        solve_chain_combine(VL.solve_chain(left, n, anchor), right, n, anchor),
        VL.solve_chain(append_chords(left, right), n, anchor), combined,
        Equal.sym(Maybe<&2, List<&2, +List<Pc.Note>>>, VL.solve_chain(append_chords(left, right), n, anchor),
          solve_chain_combine(VL.solve_chain(left, n, anchor), right, n, anchor), sc_append))
      # step : {solve_parallel_split((left,right),n,anchor) == solve_chain(append_chords(left,right),n,anchor)}
      %eapp : {VL.solve_parallel_split((left, right), n, anchor) == VL.solve_chain(_, n, anchor) :
        Maybe<&2, List<&2, +List<Pc.Note>>>}
      step

def Laws.solve_from_each_anchor_sound(h, t, right, n):
  {==}

def Laws.solve_parallel_eq_solve_chain(chords, n, anchor):
  +half = Nat.div(VL.len_chords(chords), 2n)
  solve_parallel_split_eq(VL.split_at(half, chords), n, anchor, chords, split_at_append(half, chords))

# solve_parallel_bounded is now a corollary: solve_parallel and
# solve_chain agree exactly, so whenever solve_parallel succeeds,
# solve_chain succeeds with the same solution, and solve_chain_bounded
# already covers that. chain_bounded_reanchor and chain_bounded_append
# (the old guess-then-verify seam lemmas) are gone -- there is no
# guessed anchor left to correct for.
def Laws.solve_parallel_bounded(chords, n, anchor, sol, e):
  +eq = Laws.solve_parallel_eq_solve_chain(chords, n, anchor)
  e2 = Equal.trans(Maybe<&2, List<&2, +List<Pc.Note>>>, VL.solve_chain(chords, n, anchor),
    VL.solve_parallel(chords, n, anchor), Some{sol},
    Equal.sym(Maybe<&2, List<&2, +List<Pc.Note>>>, VL.solve_parallel(chords, n, anchor),
      VL.solve_chain(chords, n, anchor), eq), e)
  Laws.solve_chain_bounded(chords, n, anchor, sol, e2)

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

# min7_shell3_sounds_root_3_7: with the root concrete, the whole
# shape computes -- both bass-string candidates, the octave choice,
# and the pitch class each sounding string lands on -- so every
# component is a literal count and closes by reflexivity. 12 cases,
# three trivial-looking but genuinely computed checks each.
def Laws.min7_shell3_sounds_root_3_7(root):
  match root:
    case Pc.C{}:
      ({==}, {==}, {==})
    case Pc.Db{}:
      ({==}, {==}, {==})
    case Pc.D{}:
      ({==}, {==}, {==})
    case Pc.Eb{}:
      ({==}, {==}, {==})
    case Pc.E{}:
      ({==}, {==}, {==})
    case Pc.F{}:
      ({==}, {==}, {==})
    case Pc.Gb{}:
      ({==}, {==}, {==})
    case Pc.G{}:
      ({==}, {==}, {==})
    case Pc.Ab{}:
      ({==}, {==}, {==})
    case Pc.A{}:
      ({==}, {==}, {==})
    case Pc.Bb{}:
      ({==}, {==}, {==})
    case Pc.B{}:
      ({==}, {==}, {==})
