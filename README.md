# Toatie

> A spicy Hardware Description Language with dependent types
> and a covid fever dream

We poke, bend, and otherwise abuse Tiny Idris --- introduced by
[Edwin Brady](https://github.com/edwinb) at
[SPLV20](https://github.com/edwinb/SPLV20).

We'll work towards:

  - [X] Let bindings (useful for sharing)
  - [X] Multi-stage core TT (See paper "A Verified Staged Interpreter is a
        Verified Compiler")
  - [ ] Command to force full evaluation at repl (useful for inspecting staged
        Code outputs)
  - [X] Separating `Parameter` types (value known at compile-time) and `Simple`
        types (value known only at circuit run-time)
  - [ ] Checking GADTs over `Simple` types for decidable sizes
  - [ ] Deriving bit representations for GADTs over `Simple` types
  - [ ] Proto-Quipper D's interpretation of dependent typing with the `Shape`
        function.
  - [ ] Conversion of Terms to something like Clash's ANF, with a little more
        unrolling.
  - [ ] Generating netlists from this ANF.
  - [ ] Encoding _synchronous_ logic

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
