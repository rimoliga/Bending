# Same as template_proof.bend with no call site at all: the identical
# error still appears, which is the clearest evidence that the body is
# checked on its own rather than per instantiation.
#
#   bend tools/issue_repro/template_proof_uncalled.bend

import Base

type Small is Type:
  Small{n: Nat, ok: {Nat.is_le(n, 5n) == True{} : Bool}}

def make(~k: Nat) -> Small:
  Small{k, {==}}

def main() -> Nat:
  0n
