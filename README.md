Adventures in Hardware with Tiny Idris
======================================

We poke, bend, and otherwise abuse Tiny Idris --- introduced by
[Edwin Brady](https://github.com/edwinb) at
[SPLV20](https://github.com/edwinb/SPLV20).

We'll work towards:

  + Let bindings (useful for sharing)
  + Separating `Parameter` types (value known at compile-time) and `Simple`
    types (value known only at circuit run-time)
  + Checking GADTs over `Simple` types for decidable sizes
  + Deriving bit representations for GADTs over `Simple` types
  + Proto-Quipper D's interpretation of dependent typing with the `Shape` function.
  + Conversion of Terms to something like Clash's ANF, with a little more unrolling.
  + Generating netlists from this ANF.
  + Encoding _synchronous_ logic
