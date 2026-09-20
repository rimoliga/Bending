# The two things that do check: inlining the construction at the call
# site, and writing one def per set of arguments -- which is what this
# project had to do for min7_shell / dom7_shell / maj7_shell.
#
#   bend tools/issue_repro/template_proof_workaround.bend

import Base

type Small is Type:
  Small{n: Nat, ok: {Nat.is_le(n, 5n) == True{} : Bool}}

def make3() -> Small:
  Small{3n, {==}}

def make4() -> Small:
  Small{4n, {==}}

def main() -> Small:
  make3()
