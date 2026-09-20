# Issue draft for bendlang/bend — not filed

This is a bug report for [bendlang/bend](https://github.com/bendlang/bend/issues),
written and verified from this project but **not submitted**: this environment's
GitHub access is scoped to `rimoliga/bending`, so creating an issue on
`bendlang/bend` was refused (`Access denied: repository "bendlang/bend" is not
configured for this session`), attaching that repository to the session was
denied by the permission layer, and there is no `gh` CLI available. Everything
below is ready to paste into a new issue as-is.

Checked against Bend 2.0.21 (source checkout at commit `6018e28`), Linux x86_64.
Searched the tracker first: [#784](https://github.com/bendlang/bend/issues/784)
is a different template problem (an open `~` argument, i.e. one that is a plain
def parameter) and [#902](https://github.com/bendlang/bend/issues/902) is about
descent through a `~` parameter, not about *when* a template body is checked.
Neither covers this.

The three repro files are in `tools/issue_repro/` so the claims below can be
re-run: `bend tools/issue_repro/template_proof.bend` (fails),
`bend tools/issue_repro/template_proof_uncalled.bend` (fails identically, with
no call site at all) and `bend tools/issue_repro/template_proof_workaround.bend`
(checks).

---

**Title:** Templates: a `~` parameter's body is checked once generically, so a `{==}` inside it can never use the call site's arguments

### What you did

```text
bun bend2/main.ts tmpl.bend --check-only
```

```bend
# tmpl.bend
import Base

type Small is Type:
  Small{n: Nat, ok: {Nat.is_le(n, 5n) == True{} : Bool}}

def make(~k: Nat) -> Small:
  Small{k, {==}}

def main() -> Small:
  make(~3n)
```

### What happened

```text
Error:
- expected : Cmp.is_le(Nat.cmp(make~k, 5n))
- observed : True{}
Location: make
6 | def make(~k: Nat) -> Small:
7>|   Small{k, {==}}
8 |
```

The only call site passes `~3n`, for which `Nat.is_le(3n, 5n)` computes to
`True{}`, so every copy the program actually compiles is well typed. The generic
body is not, and that is what gets checked.

The same file with the call removed entirely (`def main() -> Nat: 0n`) reports
the identical error, which is the clearest statement of the behaviour: the
template body is checked once, on its own, before any call site substitutes
anything. Both workarounds check fine:

```bend
def main() -> Small:            # inlined
  Small{3n, {==}}

def make3() -> Small:           # one def per value
  Small{3n, {==}}
```

A plain (non-`~`) parameter fails the same way, with `k` in place of `make~k`,
which is the point: for a proof obligation in the body, `~` currently buys
nothing over an ordinary parameter.

### Why this is surprising

`bend guide` says "Each distinct set of `~` arguments compiles to its own copy of
`twice`", which reads like monomorphization, and in C++ templates, Rust const
generics or Zig `comptime` the copy is what gets checked. Here the copy is only
compiled; the checking has already happened against an opaque `make~k`.

The consequence in practice is that a template cannot carry a proof about its
arguments. Building guitar chord voicings where the type of a field is
`{playable(strings) == True{} : Bool}`, one `shell_voicing(~third_iv,
~seventh_iv, root)` shared by every chord quality cannot close its `{==}`,
although every call site passes literals and every resulting shape is playable.
The only way to keep the proof is to write one copy of the function per set of
arguments by hand — which is exactly what the template was supposed to do.

### Expected

Any of these would resolve it, in decreasing order of usefulness:

1. Check each instantiation after substitution (in addition to, or instead of,
   the generic check), so a `{==}` in a template body may depend on its `~`
   arguments being concrete.
2. If that is not intended, say so in the guide's Templates section: `~`
   arguments are opaque while the body is checked, so a template body can prove
   nothing about them.
3. Either way, the error message could say where `make~k` comes from. `make~k` is
   not a name that appears in the source, and nothing in the message connects it
   to the `~k` parameter or explains that the body is being checked generically.

### bend --version

```text
Bend 2.0.21 (source checkout, bendlang/bend @ 6018e28, run as `bun bend2/main.ts`)
```

### uname -sm

```text
Linux x86_64
```

### clang --version (the first line)

```text
Ubuntu clang version 18.1.3 (1ubuntu1)
```
