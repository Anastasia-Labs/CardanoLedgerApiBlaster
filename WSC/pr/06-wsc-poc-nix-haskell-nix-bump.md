# SUBMISSION 4b — wsc-poc: split out the haskell.nix bump

**Repo** `input-output-hk/wsc-poc` · **commit** `97160f894a8e1d3194ef9bec309094f762497c77`
· currently sitting on `fix/benchmark-arity-and-ctx-builder` **below** the fix it has
nothing to do with · **2 files, +114/−39** (`flake.lock`, `flake.nix`)

## Why this is its own file

The branch `fix/benchmark-arity-and-ctx-builder` is **2 commits ahead of `origin/main`**,
not 1. The lower commit is a Nix toolchain bump with no relationship to the benchmark or
builder fixes. Shipping them together would mean a reviewer evaluating a `flake.lock`
churn of 144 lines in the same PR as validator-arity arithmetic, and would make either
one hard to revert without the other.

**Recommendation: cherry-pick `97160f8` onto its own branch off `origin/main`, open it as
a small separate PR, and rebase submission 4 so it carries only `c18c525`.** If the two
must ship together for CI to be green, say so explicitly in submission 4's body and note
the split was considered and rejected — do not leave it implicit.

**Open question this task could not answer:** whether `origin/main` currently builds under
Nix *without* this bump. #110 merged without it, so either main's Nix build is currently
broken for the Van Rossem index-state, or the bump is only needed for a build mode CI does
not exercise. **Determine which before deciding the order** — if main is broken, this is a
build fix that should merge *first* and fast.

---
---

# PR DESCRIPTION (submit this)

## Summary

Bumps `haskell.nix` to the pin `sc-tools` `main` uses for this cardano-api 11 stack, and
points root `nixpkgs` at `haskell-nix/nixpkgs-2411`.

The Van Rossem index-state resolves `typed-protocols 1.2.1.0`, whose **public
sublibraries** (`typed-protocols:cborg` and friends) trip a name-shadowing bug in the
previous `haskell.nix` during single-component configure — it fails with
`Dependency on unbuildable package cborg` while configuring
`typed-protocols:stateful-cborg`. `haskell.nix` `4c085ca207389ae2f2bfdc811afeebfcb326a399`
handles public sublibraries correctly.

That newer `haskell.nix` follows a `nixpkgs-unstable` which has **dropped the `ghc94x`
boot compilers** needed to bootstrap `ghc966`, so root `nixpkgs` now follows
`haskell-nix/nixpkgs-2411` instead — mirroring `sc-tools` `main`'s own wiring rather than
inventing a third combination.

## Verification

```
nix build .#regulated-stablecoin:exe:regulated-stablecoin-cli    → OK
nix build .#aiken-example:exe:cip-143-cli                        → OK
```

*(Carried from the commit's own message; **re-run both before opening**, and add whatever
else this repository's CI builds under Nix.)*

## Notes

* Pure build plumbing — no source file, no dependency version in any `.cabal`, no
  behaviour change. The `cabal` build path is untouched.
* The `haskell.nix` pin is a bare revision rather than a branch, deliberately: this
  combination is the one `sc-tools` `main` is known to work with, and a moving branch
  would silently re-break the `typed-protocols` sublibrary case.
* Root `nixpkgs` moving from `haskell-nix/nixpkgs` to `haskell-nix/nixpkgs-2411` is the
  part most worth a second opinion — it pins the whole tree to 24.11 for the sake of the
  boot compilers. If the project would rather chase `nixpkgs-unstable` and solve the
  bootstrap differently, that is a legitimate alternative and this PR is the place to say
  so.
