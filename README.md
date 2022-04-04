# Toatie

> A spicy Hardware Description Language with dependent types

We poke, bend, and otherwise abuse Tiny Idris --- introduced by [Edwin
Brady](https://github.com/edwinb) at [SPLV20](https://github.com/edwinb/SPLV20).
Our main additions to support hardware description include erasure/irrelevance of
non synthesisable terms, staging for circuit generators, deriving bit
representations, and the synthesis itself.

This is a toy language, and a work in progress toy at that 🤷

## Usage

### Building

Everything is packed up as a nix flake. If you've got the [nix package
manager](https://nixos.org/manual/nix/stable/#chap-installation), you can
rebuild the compiler with:

```console
me@computer:~/toatie $ nix build .
```

This builds the `toatie` executable found in `result/bin/` and runs all of our
tests. Example source files can be found in the `Test` directory.

### Development

We can also use the nix flake to recreate our development environment. It'll
pull in a compatible version of Idris2, its emacs mode, and expose a few handy
aliases for `toatie` development.

```console
me@computer:~/toatie $ nix develop

me@computer:~/toatie $ devEmacs #Open an emacs session with Idris2 support
me@computer:~/toatie $ devBuild #Build toatie in build/exec/
me@computer:~/toatie $ devTest  #Run all tests in Test/{good,bad}
me@computer:~/toatie $ devRepl Test/Unsigned.tt #Start the toatie REPL
```

## Examples

TODO

## Progress

We'll work towards:

  - [X] Simple let bindings
  - [X] Inline case statements (no "with" views though)
  - [X] Coverage checking and impossible clauses
  - [X] Unification similar to Idris2
  - [X] Example proofs good enough to verify binary addition
  - [X] Multi-stage core TT (See paper "A Verified Staged Interpreter is a
        Verified Compiler"; let's us unroll recursive defs of circuits in our
        source language rather than the compiler)
  - [X] Irrelevance/erasure with ICC* (See Barras' paper "The Implicit Calculus
        of Constructions as a Programming Language with Dependent Types")
  - [X] Different case tree behaviour --- implicit and quoted patterns are inaccessible
  - [X] A very simple module system (only one namespace)
  - [X] Separating type constructors into `Parameter` types (value known at compile-time) and `Simple`
        types (value known only at circuit run-time; derivable bit width)
  - [X] Checking GADTs over `Simple` types for decidable sizes
  - [X] Deriving bit representations for GADTs over `Simple` types
  - [X] Conversion of Terms to something like Clash's ANF
  - [X] Generating netlists from this ANF.
  - [ ] Encoding _synchronous_ logic

##

<pre>
"Y888888888888888888888888888888888888888888888888888888888Y"
  "Y88888888888888888888888888888888888888888888888888888Y"
   888                                                 888
   888   888                     888    d8b            888
   888   888                     888    Y8P            888
   888   888                     888                   888
   888   888888 .d88b.   8888b.  888888 888  .d88b.    888
   888   888   d88""88b     "88b 888    888 d8P  Y8b   888
   888   888   888  888 .d888888 888    888 88888888   888
   888   Y88b. Y88..88P 888  888 Y88b.  888 Y8b.       888
 .e888e   "Y888 "Y88P"  "Y888888  "Y888 888  "Y8888   e888e. 
</pre>                                               
