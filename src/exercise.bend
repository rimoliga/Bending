# exercise.bend: ii-V-I exercise generation.
#
# A guide-tone shell voicing plays just the 3rd and the 7th of a
# chord (the two notes that define its quality), on the D and G
# strings -- omitting the root and 5th, a standard, minimal jazz
# comping voicing, and exactly the two notes this milestone asks to
# mark. `up_dist_note(open, target)` is the fret, 0..11, that reaches
# `target` going up from `open`; the two candidate frets for the G
# string (that value, and the same note an octave up if it still fits
# under fret 15) are then picked between to minimize the stretch
# against the D string's fret.
#
# `shell_voicing` builds the guaranteed-playable Voicing for any root:
# it case-splits the root into its 12 concrete notes so `playable`
# fully computes in each branch, closing every branch with a bare
# `{==}` -- the same technique as Milestone 2's transpose_period12.
# If some root/quality combination ever weren't playable by this
# recipe, the corresponding branch simply wouldn't typecheck, pointing
# straight at the failing case.

import Base
import ./note.bend as Pc
import ./chord.bend as Ch
import ./voicing.bend as Vc

def le_pick(le: Bool, a: Nat, b: Nat) -> Nat:
  match le:
    case True{}:
      Nat.sub(b, a)
    case False{}:
      Nat.sub(Nat.add(b, 12n), a)

# the fret, 0..11, that reaches to_i going up from from_i (both 0..11)
def up_dist(+from_i: Nat, +to_i: Nat) -> Nat:
  le_pick(Nat.is_le(from_i, to_i), from_i, to_i)

def up_dist_note(from_n: Pc.Note, to_n: Pc.Note) -> Nat:
  up_dist(Pc.index(from_n), Pc.index(to_n))

def abs_diff_pick(le: Bool, a: Nat, b: Nat) -> Nat:
  match le:
    case True{}:
      Nat.sub(b, a)
    case False{}:
      Nat.sub(a, b)

def abs_diff(+a: Nat, +b: Nat) -> Nat:
  abs_diff_pick(Nat.is_le(a, b), a, b)

def pick_closer_pick(le: Bool, a: Nat, b: Nat) -> Nat:
  match le:
    case True{}:
      a
    case False{}:
      b

# whichever of a, b is closer to target
def pick_closer(+target: Nat, +a: Nat, +b: Nat) -> Nat:
  pick_closer_pick(Nat.is_le(abs_diff(target, a), abs_diff(target, b)), a, b)

def nearest_fret_pick(fits: Bool, target: Nat, +f0: Nat) -> Nat:
  match fits:
    case False{}:
      f0
    case True{}:
      pick_closer(target, f0, Nat.add(f0, 12n))

# f0 or f0+12 (if that's still <= 15), whichever is closer to target
def nearest_fret(target: Nat, +f0: Nat) -> Nat:
  nearest_fret_pick(Nat.is_le(Nat.add(f0, 12n), 15n), target, f0)

def guide_tone_shell(+root: Pc.Note, +third_iv: Nat, +seventh_iv: Nat) -> Vc.Strings:
  +fD = up_dist_note(Pc.D{}, Pc.transpose(third_iv, root))
  fG0 = up_dist_note(Pc.G{}, Pc.transpose(seventh_iv, root))
  Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD}, Vc.Fret{nearest_fret(fD, fG0)}, Vc.Muted{}, Vc.Muted{}}

# A shared generic def, checked once with third_iv/seventh_iv still
# abstract, can't close its {==} (a template's ~ arguments are only
# substituted at each call site's evaluation, not for this def's own
# typecheck) -- so each quality gets its own 12-way match with the
# interval literals baked directly into every branch.

def min7_shell(root: Pc.Note) -> Vc.Voicing:
  match root:
    case Pc.C{}:
      Vc.Voicing{guide_tone_shell(Pc.C{}, 3n, 10n), {==}}
    case Pc.Db{}:
      Vc.Voicing{guide_tone_shell(Pc.Db{}, 3n, 10n), {==}}
    case Pc.D{}:
      Vc.Voicing{guide_tone_shell(Pc.D{}, 3n, 10n), {==}}
    case Pc.Eb{}:
      Vc.Voicing{guide_tone_shell(Pc.Eb{}, 3n, 10n), {==}}
    case Pc.E{}:
      Vc.Voicing{guide_tone_shell(Pc.E{}, 3n, 10n), {==}}
    case Pc.F{}:
      Vc.Voicing{guide_tone_shell(Pc.F{}, 3n, 10n), {==}}
    case Pc.Gb{}:
      Vc.Voicing{guide_tone_shell(Pc.Gb{}, 3n, 10n), {==}}
    case Pc.G{}:
      Vc.Voicing{guide_tone_shell(Pc.G{}, 3n, 10n), {==}}
    case Pc.Ab{}:
      Vc.Voicing{guide_tone_shell(Pc.Ab{}, 3n, 10n), {==}}
    case Pc.A{}:
      Vc.Voicing{guide_tone_shell(Pc.A{}, 3n, 10n), {==}}
    case Pc.Bb{}:
      Vc.Voicing{guide_tone_shell(Pc.Bb{}, 3n, 10n), {==}}
    case Pc.B{}:
      Vc.Voicing{guide_tone_shell(Pc.B{}, 3n, 10n), {==}}

def dom7_shell(root: Pc.Note) -> Vc.Voicing:
  match root:
    case Pc.C{}:
      Vc.Voicing{guide_tone_shell(Pc.C{}, 4n, 10n), {==}}
    case Pc.Db{}:
      Vc.Voicing{guide_tone_shell(Pc.Db{}, 4n, 10n), {==}}
    case Pc.D{}:
      Vc.Voicing{guide_tone_shell(Pc.D{}, 4n, 10n), {==}}
    case Pc.Eb{}:
      Vc.Voicing{guide_tone_shell(Pc.Eb{}, 4n, 10n), {==}}
    case Pc.E{}:
      Vc.Voicing{guide_tone_shell(Pc.E{}, 4n, 10n), {==}}
    case Pc.F{}:
      Vc.Voicing{guide_tone_shell(Pc.F{}, 4n, 10n), {==}}
    case Pc.Gb{}:
      Vc.Voicing{guide_tone_shell(Pc.Gb{}, 4n, 10n), {==}}
    case Pc.G{}:
      Vc.Voicing{guide_tone_shell(Pc.G{}, 4n, 10n), {==}}
    case Pc.Ab{}:
      Vc.Voicing{guide_tone_shell(Pc.Ab{}, 4n, 10n), {==}}
    case Pc.A{}:
      Vc.Voicing{guide_tone_shell(Pc.A{}, 4n, 10n), {==}}
    case Pc.Bb{}:
      Vc.Voicing{guide_tone_shell(Pc.Bb{}, 4n, 10n), {==}}
    case Pc.B{}:
      Vc.Voicing{guide_tone_shell(Pc.B{}, 4n, 10n), {==}}

def maj7_shell(root: Pc.Note) -> Vc.Voicing:
  match root:
    case Pc.C{}:
      Vc.Voicing{guide_tone_shell(Pc.C{}, 4n, 11n), {==}}
    case Pc.Db{}:
      Vc.Voicing{guide_tone_shell(Pc.Db{}, 4n, 11n), {==}}
    case Pc.D{}:
      Vc.Voicing{guide_tone_shell(Pc.D{}, 4n, 11n), {==}}
    case Pc.Eb{}:
      Vc.Voicing{guide_tone_shell(Pc.Eb{}, 4n, 11n), {==}}
    case Pc.E{}:
      Vc.Voicing{guide_tone_shell(Pc.E{}, 4n, 11n), {==}}
    case Pc.F{}:
      Vc.Voicing{guide_tone_shell(Pc.F{}, 4n, 11n), {==}}
    case Pc.Gb{}:
      Vc.Voicing{guide_tone_shell(Pc.Gb{}, 4n, 11n), {==}}
    case Pc.G{}:
      Vc.Voicing{guide_tone_shell(Pc.G{}, 4n, 11n), {==}}
    case Pc.Ab{}:
      Vc.Voicing{guide_tone_shell(Pc.Ab{}, 4n, 11n), {==}}
    case Pc.A{}:
      Vc.Voicing{guide_tone_shell(Pc.A{}, 4n, 11n), {==}}
    case Pc.Bb{}:
      Vc.Voicing{guide_tone_shell(Pc.Bb{}, 4n, 11n), {==}}
    case Pc.B{}:
      Vc.Voicing{guide_tone_shell(Pc.B{}, 4n, 11n), {==}}

# ii-V-I
# ------
# ii is min7 a major 2nd (2 half steps) above the tonic, V is dom7 a
# perfect 5th (7) above, I is maj7 on the tonic itself.
#
# Each chord after the first tries to have *both* guide tones chase
# the previous chord's fret on the same string (nearest_fret on each),
# for real voice leading rather than just a compact shape in
# isolation. But chasing each string independently can pull them
# apart within one chord (e.g. D-string jumps to stay close to a
# distant previous D fret while G-string doesn't need to) -- so
# chord_step checks the chased pair's own stretch and, if it exceeds
# 4 frets, falls back to the independent, always-stretch-safe
# computation guide_tone_shell already uses (proved playable for every
# root/quality above): well-led when possible, always playable.

def pair_fst(p: Nat & Nat) -> Nat:
  match p:
    case (a, b):
      a

def pair_snd(p: Nat & Nat) -> Nat:
  match p:
    case (a, b):
      b

def stretch_ok2(+d: Nat, +g: Nat) -> Bool:
  Nat.is_le(abs_diff(d, g), 4n)

def resolve_pair_pick(ok: Bool, cd: Nat, cg: Nat, fd: Nat, fg: Nat) -> Nat & Nat:
  match ok:
    case True{}:
      (cd, cg)
    case False{}:
      (fd, fg)

# d_iv/g_iv are whichever interval (3rd or 7th) is placed on that
# string for this chord -- V swaps them relative to ii and I, because
# that is what makes the shapes actually connect: ii's 3rd is V's 7th
# (a shared or near note) and ii's 7th resolves by a half step down to
# V's 3rd, but only if each keeps the *other* string, matching real
# guide-tone-line practice.
def chord_step(prevD: Nat, prevG: Nat, +root: Pc.Note, +d_iv: Nat, +g_iv: Nat) -> Nat & Nat:
  +f0D = up_dist_note(Pc.D{}, Pc.transpose(d_iv, root))
  +f0G = up_dist_note(Pc.G{}, Pc.transpose(g_iv, root))
  +chased_d = nearest_fret(prevD, f0D)
  +chased_g = nearest_fret(prevG, f0G)
  resolve_pair_pick(stretch_ok2(chased_d, chased_g), chased_d, chased_g, f0D, nearest_fret(f0D, f0G))

def ii_pair(+tonic: Pc.Note) -> Nat & Nat:
  +root = Pc.transpose(2n, tonic)
  +f0D = up_dist_note(Pc.D{}, Pc.transpose(3n, root))
  (f0D, nearest_fret(f0D, up_dist_note(Pc.G{}, Pc.transpose(10n, root))))

def fD_ii(+tonic: Pc.Note) -> Nat:
  pair_fst(ii_pair(tonic))

def fG_ii(+tonic: Pc.Note) -> Nat:
  pair_snd(ii_pair(tonic))

# V: 7th on D (near ii's 3rd), 3rd on G (near ii's 7th) -- swapped
def v_pair(+tonic: Pc.Note) -> Nat & Nat:
  chord_step(fD_ii(tonic), fG_ii(tonic), Pc.transpose(7n, tonic), 10n, 4n)

def fD_V(+tonic: Pc.Note) -> Nat:
  pair_fst(v_pair(tonic))

def fG_V(+tonic: Pc.Note) -> Nat:
  pair_snd(v_pair(tonic))

# I: 3rd on D (near V's 7th), 7th on G (near V's 3rd) -- back to normal
def i_pair(+tonic: Pc.Note) -> Nat & Nat:
  chord_step(fD_V(tonic), fG_V(tonic), tonic, 4n, 11n)

def fD_I(+tonic: Pc.Note) -> Nat:
  pair_fst(i_pair(tonic))

def fG_I(+tonic: Pc.Note) -> Nat:
  pair_snd(i_pair(tonic))

# guaranteed playable, by the same 12-way-match-then-{==} technique as
# min7_shell/dom7_shell/maj7_shell above.
def ii_v_i_shells(tonic: Pc.Note) -> Vc.Voicing & Vc.Voicing & Vc.Voicing:
  match tonic:
    case Pc.C{}:
      (Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_ii(Pc.C{})}, Vc.Fret{fG_ii(Pc.C{})}, Vc.Muted{}, Vc.Muted{}}, {==}},
       Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_V(Pc.C{})}, Vc.Fret{fG_V(Pc.C{})}, Vc.Muted{}, Vc.Muted{}}, {==}},
       Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_I(Pc.C{})}, Vc.Fret{fG_I(Pc.C{})}, Vc.Muted{}, Vc.Muted{}}, {==}})
    case Pc.Db{}:
      (Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_ii(Pc.Db{})}, Vc.Fret{fG_ii(Pc.Db{})}, Vc.Muted{}, Vc.Muted{}}, {==}},
       Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_V(Pc.Db{})}, Vc.Fret{fG_V(Pc.Db{})}, Vc.Muted{}, Vc.Muted{}}, {==}},
       Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_I(Pc.Db{})}, Vc.Fret{fG_I(Pc.Db{})}, Vc.Muted{}, Vc.Muted{}}, {==}})
    case Pc.D{}:
      (Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_ii(Pc.D{})}, Vc.Fret{fG_ii(Pc.D{})}, Vc.Muted{}, Vc.Muted{}}, {==}},
       Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_V(Pc.D{})}, Vc.Fret{fG_V(Pc.D{})}, Vc.Muted{}, Vc.Muted{}}, {==}},
       Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_I(Pc.D{})}, Vc.Fret{fG_I(Pc.D{})}, Vc.Muted{}, Vc.Muted{}}, {==}})
    case Pc.Eb{}:
      (Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_ii(Pc.Eb{})}, Vc.Fret{fG_ii(Pc.Eb{})}, Vc.Muted{}, Vc.Muted{}}, {==}},
       Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_V(Pc.Eb{})}, Vc.Fret{fG_V(Pc.Eb{})}, Vc.Muted{}, Vc.Muted{}}, {==}},
       Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_I(Pc.Eb{})}, Vc.Fret{fG_I(Pc.Eb{})}, Vc.Muted{}, Vc.Muted{}}, {==}})
    case Pc.E{}:
      (Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_ii(Pc.E{})}, Vc.Fret{fG_ii(Pc.E{})}, Vc.Muted{}, Vc.Muted{}}, {==}},
       Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_V(Pc.E{})}, Vc.Fret{fG_V(Pc.E{})}, Vc.Muted{}, Vc.Muted{}}, {==}},
       Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_I(Pc.E{})}, Vc.Fret{fG_I(Pc.E{})}, Vc.Muted{}, Vc.Muted{}}, {==}})
    case Pc.F{}:
      (Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_ii(Pc.F{})}, Vc.Fret{fG_ii(Pc.F{})}, Vc.Muted{}, Vc.Muted{}}, {==}},
       Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_V(Pc.F{})}, Vc.Fret{fG_V(Pc.F{})}, Vc.Muted{}, Vc.Muted{}}, {==}},
       Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_I(Pc.F{})}, Vc.Fret{fG_I(Pc.F{})}, Vc.Muted{}, Vc.Muted{}}, {==}})
    case Pc.Gb{}:
      (Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_ii(Pc.Gb{})}, Vc.Fret{fG_ii(Pc.Gb{})}, Vc.Muted{}, Vc.Muted{}}, {==}},
       Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_V(Pc.Gb{})}, Vc.Fret{fG_V(Pc.Gb{})}, Vc.Muted{}, Vc.Muted{}}, {==}},
       Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_I(Pc.Gb{})}, Vc.Fret{fG_I(Pc.Gb{})}, Vc.Muted{}, Vc.Muted{}}, {==}})
    case Pc.G{}:
      (Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_ii(Pc.G{})}, Vc.Fret{fG_ii(Pc.G{})}, Vc.Muted{}, Vc.Muted{}}, {==}},
       Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_V(Pc.G{})}, Vc.Fret{fG_V(Pc.G{})}, Vc.Muted{}, Vc.Muted{}}, {==}},
       Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_I(Pc.G{})}, Vc.Fret{fG_I(Pc.G{})}, Vc.Muted{}, Vc.Muted{}}, {==}})
    case Pc.Ab{}:
      (Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_ii(Pc.Ab{})}, Vc.Fret{fG_ii(Pc.Ab{})}, Vc.Muted{}, Vc.Muted{}}, {==}},
       Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_V(Pc.Ab{})}, Vc.Fret{fG_V(Pc.Ab{})}, Vc.Muted{}, Vc.Muted{}}, {==}},
       Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_I(Pc.Ab{})}, Vc.Fret{fG_I(Pc.Ab{})}, Vc.Muted{}, Vc.Muted{}}, {==}})
    case Pc.A{}:
      (Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_ii(Pc.A{})}, Vc.Fret{fG_ii(Pc.A{})}, Vc.Muted{}, Vc.Muted{}}, {==}},
       Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_V(Pc.A{})}, Vc.Fret{fG_V(Pc.A{})}, Vc.Muted{}, Vc.Muted{}}, {==}},
       Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_I(Pc.A{})}, Vc.Fret{fG_I(Pc.A{})}, Vc.Muted{}, Vc.Muted{}}, {==}})
    case Pc.Bb{}:
      (Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_ii(Pc.Bb{})}, Vc.Fret{fG_ii(Pc.Bb{})}, Vc.Muted{}, Vc.Muted{}}, {==}},
       Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_V(Pc.Bb{})}, Vc.Fret{fG_V(Pc.Bb{})}, Vc.Muted{}, Vc.Muted{}}, {==}},
       Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_I(Pc.Bb{})}, Vc.Fret{fG_I(Pc.Bb{})}, Vc.Muted{}, Vc.Muted{}}, {==}})
    case Pc.B{}:
      (Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_ii(Pc.B{})}, Vc.Fret{fG_ii(Pc.B{})}, Vc.Muted{}, Vc.Muted{}}, {==}},
       Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_V(Pc.B{})}, Vc.Fret{fG_V(Pc.B{})}, Vc.Muted{}, Vc.Muted{}}, {==}},
       Vc.Voicing{Vc.Strings{Vc.Muted{}, Vc.Muted{}, Vc.Fret{fD_I(Pc.B{})}, Vc.Fret{fG_I(Pc.B{})}, Vc.Muted{}, Vc.Muted{}}, {==}})

# The two ii-V-i progressions, as chords
# --------------------------------------
# Chord-level (not fretboard-level) progressions, the form
# voicelead.bend's solve_chain consumes. The minor one is the reason
# chord.bend grew min7b5: iiø7 - V7 - im7 is the minor-key cadence
# most standards actually run on.

def major_ii_v_i(+tonic: Pc.Note) -> +List<Ch.Chord>:
  [Ch.min7(Pc.transpose(2n, tonic)), Ch.dom7(Pc.transpose(7n, tonic)), Ch.maj7(tonic)]

def minor_ii_v_i(+tonic: Pc.Note) -> +List<Ch.Chord>:
  [Ch.min7b5(Pc.transpose(2n, tonic)), Ch.dom7(Pc.transpose(7n, tonic)), Ch.min7(tonic)]

# Cycle of fourths
# ----------------
# Repeatedly transposing by a perfect 4th (5 half steps) visits every
# pitch class exactly once before returning to the start, since 5 and
# 12 share no factor -- the standard reason the cycle of fourths (or
# fifths) is a full tour, not a shorter loop. `cycle_of_fourths_go`
# just iterates `transpose(5, _)` 12 times.

def cycle_of_fourths_go(remaining: Nat, +n: Pc.Note) -> List<Pc.Note>:
  match remaining:
    case 0n:
      Nil{}
    case 1n+r:
      n <> cycle_of_fourths_go(r, Pc.transpose(5n, n))

def cycle_of_fourths(start: Pc.Note) -> List<Pc.Note>:
  cycle_of_fourths_go(12n, start)
