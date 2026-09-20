# Repro for ISSUE_DRAFT.md: a template's body is typechecked once,
# generically, before any call site substitutes its ~ arguments -- so
# the {==} below cannot see that k is 3n at the only call site.
#
#   bend tools/issue_repro/template_proof.bend
#
# Error:
# - expected : Cmp.is_le(Nat.cmp(make~k, 5n))
# - observed : True{}
# Location: make

import Base

type Small is Type:
  Small{n: Nat, ok: {Nat.is_le(n, 5n) == True{} : Bool}}

def make(~k: Nat) -> Small:
  Small{k, {==}}

def main() -> Small:
  make(~3n)
